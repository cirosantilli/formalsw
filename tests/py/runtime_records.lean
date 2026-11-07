import lang.py.FormalSW.HeapRuntimeCostRecords
import lang.py.FormalSW.HeapRuntimeCostListCopies

open FormalSW.PyAst HeapCalls HeapCalls.Runtime
private def fields : List Arg :=
  [⟨"x", some (.name "int"), none⟩, ⟨"y", none, none⟩]
private def program : Module :=
  { body := [.classDef "Point" [.dataclassFields true fields]], classOrigins := [("Point", "example")] }
private def point (x y : Mutable.Value) : Mutable.Object :=
  .dataInstance "example" "Point" true ["x", "y"] [("x", x), ("y", y)]

/-- Construction copies field references uniformly in their integer widths and referents. -/
example (x y : Mutable.Value) (heap : Heap) (arithmetic : PrimitiveWork.Arithmetic) :
    ReturnsIn arithmetic program "Point" [x, y] heap 6 (.ref heap.length) (heap ++ [point x y]) :=
  ReturnsIn.dataclass_constructor (fields := fields) rfl rfl rfl rfl rfl rfl

/-- A newly constructed record can be read through the actual call and field expression. -/
example (n : Int) : EvaluatesIn .word program (fun _ => some (.scalar (.int n)))
    (.attribute (.call (.name "Point") [.name "n", .constant (.int 7)]) "x")
    [] 21 (.scalar (.int n)) [point (.scalar (.int n)) (.scalar (.int 7))] := by
  apply EvaluatesIn.field (budget := 12) (work := 7)
  · exact EvaluatesIn.call (ArgumentsIn.cons (EvaluatesIn.lookup rfl)
      (ArgumentsIn.cons EvaluatesIn.constant ArgumentsIn.nil))
      (ReturnsIn.dataclass_constructor (fields := fields) rfl rfl rfl rfl rfl rfl)
  · simp [getAttribute, instanceClass, program, Module.findClass, Module.findClassBody, findClassBodyIn, point]
  · simp [RecordWork.field, RecordWork.lookup, point, List.lookup]
    rfl

/-- Reading a stored pointer does not traverse or copy its potentially large referent. -/
example (items : List Mutable.Value) :
    RecordWork.field [.list items, point (.scalar (.int 0)) (.ref 0)] (.ref 1) "y" = some 7 := rfl
example : RecordWork.field [point (.scalar .none) (.scalar .none)] (.ref 0) "missing" = none := rfl
example : RecordWork.field [point (.scalar .none) (.scalar .none)] (.ref 0) "__class__" = none := rfl
example : RecordWork.field [.list []] (.ref 0) "x" = none := rfl
example (count : Nat) : RecordWork.lookup "x" (List.replicate count ("long name", .scalar .none)) =
    11*count+1 := by
  have lengths : "long name".length + "x".length + 1 = 11 := by decide
  simp [RecordWork.lookup, lengths, Nat.mul_comm]

example : RecordWork.construct program "Point" [] = none := rfl
example : RecordWork.construct program "Unknown" [] = none := rfl
private def custom : Module :=
  { body := [.classDef "Point" [.dataclassFields true fields, .functionDef "__init__" [] none []]],
    classOrigins := [("Point", "example")] }
example : RecordWork.construct custom "Point" [.scalar (.int 1), .scalar (.int 2)] = some 4 := rfl
