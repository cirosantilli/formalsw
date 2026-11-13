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
