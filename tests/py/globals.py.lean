import «.formalsw».tests.py.«globals.py.ast»
import FormalSW

open FormalSW.PyAst

namespace tests.py.globals

private abbrev call (name : String) (args : List Constant) (state : ScalarGlobals) :=
  scalarFunctionWithGlobals GlobalsAst.module name args state

private theorem offset_done (n offset : Int) :
    (call "add_offset" [.int n] [("offset", .int offset)]).Finishes
      (.ok (.int (n + offset))) [("offset", .int offset)] := by
  apply ScalarCall.finishes_of_observe (fuel := 2)
  rfl

private theorem commuted_done (n offset : Int) :
    (call "add_offset_commuted" [.int n] [("offset", .int offset)]).Finishes
      (.ok (.int (n + offset))) [("offset", .int offset)] := by
  have observed : (call "add_offset_commuted" [.int n] [("offset", .int offset)]).execution.observe 2 =
      .done (.ok ⟨.ok (.int (offset + n)), [("offset", .int offset)]⟩) := by rfl
  simpa [Int.add_comm] using ScalarCall.finishes_of_observe observed

private theorem advance_done (n total : Int) :
    (call "advance" [.int n] [("total", .int total)]).Finishes
      (.ok (.int (total + n))) [("total", .int (total + n))] := by
  apply ScalarCall.finishes_of_observe (fuel := 4)
  rfl

private theorem explicit_done (n total : Int) :
    (call "advance_explicit" [.int n] [("total", .int total)]).Finishes
      (.ok (.int (total + n))) [("total", .int (total + n))] := by
  apply ScalarCall.finishes_of_observe (fuel := 4)
  rfl

private theorem raised_done (n total : Int) :
    (call "raise_after" [.int n] [("total", .int total)]).Finishes
      (.error { typeName := "ValueError", args := [.string "failure"] })
      [("total", .int (total + n))] := by
  apply ScalarCall.finishes_of_observe (fuel := 4)
  rfl


theorem add_offset.«Returns» :
    ∀ (n : Int) (offset : Int),
    (FormalSW.PyAst.scalarFunctionWithGlobals GlobalsAst.module "add_offset" [.int n] [("offset", .int offset)]).Returns
  := by
  intro n offset
  exact ⟨_, _, offset_done n offset⟩

theorem add_offset.«Halts» :
    ∀ (n : Int) (offset : Int),
    (FormalSW.PyAst.scalarFunctionWithGlobals GlobalsAst.module "add_offset" [.int n] [("offset", .int offset)]).Halts
  := by
  intro n offset
  exact (ScalarCall.returns_iff_halts_not_throws _).mp (add_offset.«Returns» n offset) |>.1

theorem add_offset.«Not Throws» :
    Not (∃ (n : Int) (offset : Int),
    (FormalSW.PyAst.scalarFunctionWithGlobals GlobalsAst.module "add_offset" [.int n] [("offset", .int offset)]).Throws)
  := by
  rintro ⟨n, offset, thrown⟩
  exact ((ScalarCall.returns_iff_halts_not_throws _).mp (add_offset.«Returns» n offset)).2 thrown

theorem add_offset.«ReturnType» :
    ∀ (n : Int) (offset : Int),
    (FormalSW.PyAst.scalarFunctionWithGlobals GlobalsAst.module "add_offset" [.int n] [("offset", .int offset)]).ReturnType "int"
  := by
  intro n offset
  exact Or.inr ⟨_, _, offset_done n offset, rfl⟩

theorem add_offset.returns_with_offset :
    let _this_module := GlobalsAst.module;
    ∀ (n offset : Int),
    let this_function := fun (input_0 : Int) => FormalSW.PyAst.scalarFunctionWithGlobals GlobalsAst.module "add_offset" [.int input_0] [("offset", .int offset)];
    Returns(this_function(n))
  := by
  exact add_offset.«Returns»

theorem add_offset_commuted.«Equiv(add_offset)» :
    ∀ (n : Int) (offset : Int),
    (FormalSW.PyAst.scalarFunctionWithGlobals GlobalsAst.module "add_offset_commuted" [.int n] [("offset", .int offset)]).Equiv (FormalSW.PyAst.scalarFunctionWithGlobals GlobalsAst.module "add_offset" [.int n] [("offset", .int offset)])
  := by
  intro n offset
  exact ScalarCall.equiv_of_finishes (commuted_done n offset) (offset_done n offset)

theorem advance.«Returns» :
    ∀ (n : Int) (total : Int),
    (FormalSW.PyAst.scalarFunctionWithGlobals GlobalsAst.module "advance" [.int n] [("total", .int total)]).Returns
  := by
  intro n total
  exact ⟨_, _, advance_done n total⟩

theorem advance_explicit.«Equiv(advance)» :
    ∀ (n : Int) (total : Int),
    (FormalSW.PyAst.scalarFunctionWithGlobals GlobalsAst.module "advance_explicit" [.int n] [("total", .int total)]).Equiv (FormalSW.PyAst.scalarFunctionWithGlobals GlobalsAst.module "advance" [.int n] [("total", .int total)])
  := by
  intro n total
  exact ScalarCall.equiv_of_finishes (explicit_done n total) (advance_done n total)

theorem advance_explicit.«EquivReturn(advance)» :
    ∀ (n : Int) (total : Int),
    (FormalSW.PyAst.scalarFunctionWithGlobals GlobalsAst.module "advance_explicit" [.int n] [("total", .int total)]).EquivReturn (FormalSW.PyAst.scalarFunctionWithGlobals GlobalsAst.module "advance" [.int n] [("total", .int total)])
  := by
  intro n total
  exact (advance_explicit.«Equiv(advance)» n total).equivReturn

theorem return_only.«Not Equiv(advance)» :
    Not (∀ (n : Int) (total : Int),
    (FormalSW.PyAst.scalarFunctionWithGlobals GlobalsAst.module "return_only" [.int n] [("total", .int total)]).Equiv (FormalSW.PyAst.scalarFunctionWithGlobals GlobalsAst.module "advance" [.int n] [("total", .int total)]))
  := by
  intro h
  have unchanged : (call "return_only" [.int 1] [("total", .int 0)]).Finishes
      (.ok (.int 1)) [("total", .int 0)] :=
    ScalarCall.finishes_of_observe (fuel := 2) (by rfl)
  have impossible := ((h 1 0 _ _).mp unchanged).unique (advance_done 1 0)
  cases impossible

theorem raise_after.«Halts» :
    ∀ (n : Int) (total : Int),
    (FormalSW.PyAst.scalarFunctionWithGlobals GlobalsAst.module "raise_after" [.int n] [("total", .int total)]).Halts
  := by
  intro n total
  exact ⟨_, _, raised_done n total⟩

theorem raise_after.«Throws» :
    ∃ (n : Int) (total : Int),
    (FormalSW.PyAst.scalarFunctionWithGlobals GlobalsAst.module "raise_after" [.int n] [("total", .int total)]).Throws
  := by
  exact ⟨1, 0, _, _, raised_done 1 0⟩

theorem raise_after.«Not Equiv(raise_before)» :
    Not (∀ (n : Int) (total : Int),
    (FormalSW.PyAst.scalarFunctionWithGlobals GlobalsAst.module "raise_after" [.int n] [("total", .int total)]).Equiv (FormalSW.PyAst.scalarFunctionWithGlobals GlobalsAst.module "raise_before" [.int n] [("total", .int total)]))
  := by
  intro h
  have before : (call "raise_before" [.int 1] [("total", .int 0)]).Finishes
      (.error { typeName := "ValueError", args := [.string "failure"] }) [("total", .int 0)] :=
    ScalarCall.finishes_of_observe (fuel := 2) (by rfl)
  have impossible := ((h 1 0 _ _).mp (raised_done 1 0)).unique before
  cases impossible

theorem read_label.«Returns» :
    ∀ (label : String),
    (FormalSW.PyAst.scalarFunctionWithGlobals GlobalsAst.module "read_label" [] [("label", .string label)]).Returns
  := by
  intro label
  exact ⟨.string label, [("label", .string label)], ScalarCall.finishes_of_observe (fuel := 2) (by rfl)⟩

theorem read_label.«ReturnType» :
    ∀ (label : String),
    (FormalSW.PyAst.scalarFunctionWithGlobals GlobalsAst.module "read_label" [] [("label", .string label)]).ReturnType "str"
  := by
  intro label
  exact Or.inr ⟨.string label, [("label", .string label)], ScalarCall.finishes_of_observe (fuel := 2) (by rfl), rfl⟩

theorem read_enabled.«Returns» :
    ∀ (enabled : Bool),
    (FormalSW.PyAst.scalarFunctionWithGlobals GlobalsAst.module "read_enabled" [] [("enabled", .bool enabled)]).Returns
  := by
  intro enabled
  exact ⟨.bool enabled, [("enabled", .bool enabled)], ScalarCall.finishes_of_observe (fuel := 2) (by rfl)⟩

-- A declaration in an unexecuted branch still determines Python scope.
theorem advance_declared_in_branch.«Equiv(advance)» (n total : Int) :
    (call "advance_declared_in_branch" [.int n] [("total", .int total)]).Equiv
      (call "advance" [.int n] [("total", .int total)]) := by
  apply ScalarCall.equiv_of_finishes (hr := advance_done n total)
  apply ScalarCall.finishes_of_observe (fuel := 4)
  rfl

theorem parameter_named_total.«Not Equiv(read_total)» :
    ¬ (∀ (total global_total : Int),
      (call "parameter_named_total" [.int total] [("total", .int global_total)]).Equiv
        (call "read_total" [.int total] [("total", .int global_total)])) := by
  intro h
  have fromArg : (call "parameter_named_total" [.int 1] [("total", .int 0)]).Finishes
      (.ok (.int 1)) [("total", .int 0)] :=
    ScalarCall.finishes_of_observe (fuel := 2) (by rfl)
  have fromGlobal : (call "read_total" [.int 1] [("total", .int 0)]).Finishes
      (.ok (.int 0)) [("total", .int 0)] :=
    ScalarCall.finishes_of_observe (fuel := 2) (by rfl)
  have impossible := ((h 1 0 _ _).mp fromArg).unique fromGlobal
  cases impossible

-- A local with the same spelling does not overwrite the supplied global.
example (n total : Int) :
    (call "local_total" [.int n] [("total", .int total)]).Finishes
      (.ok (.int n)) [("total", .int total)] := by
  apply ScalarCall.finishes_of_observe (fuel := 3)
  rfl

end tests.py.globals
