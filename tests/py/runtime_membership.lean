import lang.py.FormalSW.HeapRuntimeCostMembership

open FormalSW.PyAst HeapCalls HeapCalls.Runtime
private def program : Module := { body := [] }

example (needle : Int) (items : List Int) :
    operation .word [.tuple (items.map (fun n => .scalar (.int n)))] (.membership false)
      [.scalar (.int needle), .ref 0] = some (3*items.length+1) :=
  sequenceMembership_integers needle items

/-- Building the tuple and scanning it are both charged. -/
example : EvaluatesIn .word program (fun _ => none)
    (.membership (.constant (.int 1)) (.tuple [.constant (.int 1), .constant (.int 2)]) false)
    [] 23 (.scalar (.bool true)) [.tuple [.scalar (.int 1), .scalar (.int 2)]] := by
  apply EvaluatesIn.membership (budget := 14) (work := 7)
    (value := .scalar (.int 1)) (receiver := .ref 0)
  · exact ArgumentsIn.cons EvaluatesIn.constant
      (ArgumentsIn.cons (EvaluatesIn.tuple
        (ArgumentsIn.cons EvaluatesIn.constant (ArgumentsIn.cons EvaluatesIn.constant ArgumentsIn.nil)) (by simp)) ArgumentsIn.nil)
  · rfl
  · rfl

example : operation .word [.list []] (.membership true) [.scalar (.int 1), .ref 0] = some 1 := rfl
example : operation .bits [.tuple [.scalar (.int 1024), .scalar (.int 0)]] (.membership false)
    [.scalar (.int 1), .ref 0] = some 17 := rfl
example : operation .word [.tuple [.ref 1]] (.membership false) [.ref 2, .ref 0] = none := rfl

/-- Sequence support preserves dictionary representation and key costs. -/
example : operation .word [.dict [(.int 1, .scalar .none), (.int 2, .scalar .none)]]
    (.membership false) [.scalar (.int 3), .ref 0] = some 9 := rfl
example : operation .word [.dict [(.int 1, .scalar .none), (.int 2, .scalar .none)]]
    (.membership false) [.scalar (.int 3), .ref 0] .balancedTree = some 15 := rfl

/-- Scalar sets use the same worst-case search convention, including Python's
equality between Boolean True and integer one. -/
example (env : HeapCalls.Env) (get : env "s" = some (.ref 0)) :
    EvaluatesIn .word program env (.membership (.constant (.bool true)) (.name "s") false)
      [.set [.int 1]] 13 (.scalar (.bool true)) [.set [.int 1]] := by
  apply EvaluatesIn.membership (budget := 5) (work := 6)
    (ArgumentsIn.cons EvaluatesIn.constant (ArgumentsIn.cons (EvaluatesIn.lookup get) ArgumentsIn.nil))
  · rfl
  · rfl

example : operation .word [.set []] (.membership true) [.scalar (.int 1), .ref 0] = some 3 := rfl
example : operation .word [.set [.int 1, .int 2]] (.membership false)
    [.scalar (.int 3), .ref 0] = some 9 := rfl
example : operation .word [.set [.int 1, .int 2]] (.membership false)
    [.scalar (.int 3), .ref 0] .balancedTree = some 15 := rfl
example : operation .word [.set [.string "ABCDEFGH"]] (.membership false)
    [.scalar (.string "A"), .ref 0] = some 24 := rfl
example : operation .word [.set [.int 1]] (.membership false) [.ref 1, .ref 0] = none := rfl
