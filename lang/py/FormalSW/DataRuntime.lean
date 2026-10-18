import lang.py.FormalSW.Python
import lang.py.FormalSW.Runtime

/-! An interpreter for read-only Python data programs: scalars, nested lists,
local assignment, conditionals, loops, and len/type. Lists cannot be mutated in
this subset, so a tree representation preserves Python's observable behavior.
This is a general interpreter, not a recognizer for the graph comparator. -/

namespace FormalSW.PyAst

inductive Data where
  | scalar (value : Constant)
  | list (items : List Data)
  | type (name : String)
deriving Repr, BEq, Lean.ToExpr

def Data.typeName : Data → String
  | .scalar (.int _) => "int"
  | .scalar (.bool _) => "bool"
  | .scalar (.string _) => "str"
  | .scalar .none => "NoneType"
  | .list _ => "list"
  | .type _ => "type"

def Data.truth : Data → Bool
  | .scalar c => scalarTruth c
  | .list xs => !xs.isEmpty
  | .type _ => true

/- Python equality on this closed data domain, including True == 1. -/
mutual
  def Data.equal : Data → Data → Bool
    | .scalar a, .scalar b => (scalarCompare .eq a b).getD false
    | .list xs, .list ys => dataListEqual xs ys
    | .type a, .type b => a == b
    | _, _ => false
  def dataListEqual : List Data → List Data → Bool
    | [], [] => true
    | a :: xs, b :: ys => a.equal b && dataListEqual xs ys
    | _, _ => false
end

abbrev DataEnv := String → Option Data

def DataEnv.set (env : DataEnv) (name : String) (value : Data) : DataEnv :=
  fun query => if query = name then some value else env query

private def dataError (name : String) : Except ExceptionObject α :=
  .error { typeName := name, args := [] }

def dataExpr (env : DataEnv) : Expr → Option (Except ExceptionObject Data)
  | .constant c => some (.ok (.scalar c))
  | .name name => some <| match env name with
      | some value => .ok value
      | none => if name ∈ ["int", "bool", "str", "list"] then .ok (.type name)
          else dataError "UnboundLocalError"
  | .list items => do
      let values ← items.mapM (dataExpr env)
      return Data.list <$> (values.mapM id)
  | .subscript collection index => do
      let collection ← dataExpr env collection
      let index ← dataExpr env index
      match collection, index with
      | .error e, _ | _, .error e => return .error e
      | .ok collection, .ok index =>
        let index := match index with
          | .scalar (.bool b) => Data.scalar (.int (if b then 1 else 0))
          | other => other
        let items := match collection with
          | .list xs => some xs
          | .scalar (.string s) => some (s.toList.map (Data.scalar ∘ Constant.string ∘ String.singleton))
          | _ => none
        match items, index with
        | some xs, .scalar (.int i) =>
            let i := if i < 0 then i + xs.length else i
            if i < 0 then return dataError "IndexError"
            else match xs[i.toNat]? with
              | some value => return .ok value
              | none => return dataError "IndexError"
        | _, _ => match collection with
            | .type _ => none -- e.g. list[int] is outside this interpreter.
            | _ => return dataError "TypeError"
  | .call (.name "type") [arg] => do
      let value ← dataExpr env arg
      return (fun v => Data.type v.typeName) <$> value
  | .call (.name "len") [arg] => do
      let value ← dataExpr env arg
      return do
        match ← value with
        | .list xs => .ok (.scalar (.int xs.length))
        | .scalar (.string s) => .ok (.scalar (.int s.length))
        | _ => dataError "TypeError"
  | .binOp left op right => do
      let left ← dataExpr env left
      let right ← dataExpr env right
      match left, right with
      | .error e, _ | _, .error e => return .error e
      | .ok (.list xs), .ok (.list ys) => match op with
          | .add => return .ok (.list (xs ++ ys))
          | _ => return dataError "TypeError"
      | .ok (.scalar a), .ok (.scalar b) =>
          let number : Constant → Constant
            | .bool b => .int (if b then 1 else 0)
            | c => c
          match op, a, b with
          | .add, .string a, .string b => return .ok (.scalar (.string (a ++ b)))
          | _, _, _ => return (← scalarBinary op (number a) (number b)).map Data.scalar
      | _, _ => return dataError "TypeError"
  | .unaryOp op operand => do
      let value ← dataExpr env operand
      return do
        let value ← value
        match op, value with
        | .not, value => .ok (.scalar (.bool (!value.truth)))
        | .uSub, .scalar (.int n) => .ok (.scalar (.int (-n)))
        | .uSub, .scalar (.bool b) => .ok (.scalar (.int (if b then -1 else 0)))
        | _, _ => dataError "TypeError"
  | .compare left [(op, right)] => do
      let left ← dataExpr env left
      let right ← dataExpr env right
      match op, left, right with
      | .lt, .ok (.list _), .ok (.list _)
      | .ltE, .ok (.list _), .ok (.list _)
      | .gt, .ok (.list _), .ok (.list _)
      | .gtE, .ok (.list _), .ok (.list _) => none
      | _, _, _ => do
        return do
          let left ← left
          let right ← right
          match op with
          | .eq => .ok (.scalar (.bool (left.equal right)))
          | .notEq => .ok (.scalar (.bool (!left.equal right)))
          | _ => match left, right with
              | .scalar a, .scalar b => match scalarCompare op a b with
                  | some value => .ok (.scalar (.bool value))
                  | none => dataError "TypeError"
              | _, _ => dataError "TypeError"
  | _ => none

structure DataState where
  todo : List Stmt
  env : DataEnv

def dataStep (state : DataState) : Step DataState Data :=
  let ⟨todo, env⟩ := state
  match todo with
  | [] => .done (.ok (.scalar .none))
  | .return expr :: _ => match dataExpr env expr with
      | some outcome => .done outcome
      | none => .unsupported
  | .assign [.name name] expr :: rest => match dataExpr env expr with
      | some (.ok value) => .next ⟨rest, env.set name value⟩
      | some (.error e) => .done (.error e)
      | none => .unsupported
  | .ifThen condition yes no :: rest => match dataExpr env condition with
      | some (.ok value) => .next ⟨(if value.truth then yes else no) ++ rest, env⟩
      | some (.error e) => .done (.error e)
      | none => .unsupported
  | .whileDo condition body otherwise :: rest => match dataExpr env condition with
      | some (.ok value) => .next ⟨if value.truth then
          body ++ [.whileDo condition body otherwise] ++ rest else otherwise ++ rest, env⟩
      | some (.error e) => .done (.error e)
      | none => .unsupported
  | .expr expr :: rest => match dataExpr env expr with
      | some (.ok _) => .next ⟨rest, env⟩
      | some (.error e) => .done (.error e)
      | none => .unsupported
  | _ => .unsupported

def dataFunction (module : Module) (name : String) (values : List Data) : Execution Data :=
  match findFunctionIn module.body name with
  | some (args, body) =>
      if args.length = values.length then
        ⟨DataState, ⟨executableBody body, fun name => ((args.map Arg.name).zip values).lookup name⟩,
          dataStep⟩
      else Execution.unsupported
  | none => Execution.unsupported

end FormalSW.PyAst

/-- Parse Python through the normal AST bridge and validate the entire data subset.
Use include_str so Lake tracks changes to the actual Python definition. -/
syntax "python_data% " term : term

open Lean Elab Term Meta in
elab_rules : term
  | `(python_data% $source:term) => do
      let expr ← elabTerm source (some (mkConst ``String))
      let some text := getStringValue? expr
        | throwError "python_data% expects a string literal or include_str"
      let result ← FormalSW.PyAst.runPythonCompiler "lang.py.data_ast" #[(toJson text).compress]
      if result.exitCode != 0 then throwError "{result.stderr}"
      let json ← ofExcept (Json.parse result.stdout)
      return Lean.toExpr (← ofExcept (FormalSW.PyAst.Module.fromJsonDocument? json))
