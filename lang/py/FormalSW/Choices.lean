import lang.py.FormalSW.MutableGlobals

/-! Unspecified choices are universally quantified in guaranteed properties.
An execution may consult an arbitrary sequence of natural numbers. This does
not impose a fuel bound, a preferred order, or a fairness assumption. -/
namespace FormalSW.PyAst

abbrev ChoiceSchedule := Nat → Nat

structure ExecutionFamily (α : Type) where
  run : ChoiceSchedule → Execution α

namespace ExecutionFamily

def Returns (family : ExecutionFamily α) : Prop := ∀ choices, (family.run choices).Returns
def Throws (family : ExecutionFamily α) : Prop := ∀ choices, (family.run choices).Throws
def Halts (family : ExecutionFamily α) : Prop := ∀ choices, (family.run choices).Halts
def Diverges (family : ExecutionFamily α) : Prop := ∀ choices, (family.run choices).Diverges
def Supported (family : ExecutionFamily α) : Prop := ∀ choices, (family.run choices).Supported

/-- Guaranteed equivalence allows the two executions to make independent choices.
Thus an order-sensitive result cannot establish this property even against itself. -/
def Equiv (left right : ExecutionFamily α) : Prop :=
  ∀ a b, (left.run a).Equiv (right.run b)
def EquivReturn (left right : ExecutionFamily α) : Prop :=
  ∀ a b, (left.run a).EquivReturn (right.run b)
def ReturnType (family : ExecutionFamily Constant) (kind : String) : Prop :=
  ∀ choices, (family.run choices).ReturnType kind

def deterministic (execution : Execution α) : ExecutionFamily α := ⟨fun _ => execution⟩

theorem Returns.supported {family : ExecutionFamily α} (h : family.Returns) : family.Supported :=
  fun choices => (h choices).supported

end ExecutionFamily

namespace Mutable

structure CallFamily where
  run : ChoiceSchedule → Call

namespace CallFamily

def Returns (family : CallFamily) : Prop := ∀ choices, (family.run choices).Returns
def Throws (family : CallFamily) : Prop := ∀ choices, (family.run choices).Throws
def Halts (family : CallFamily) : Prop := ∀ choices, (family.run choices).Halts
def Diverges (family : CallFamily) : Prop := ∀ choices, (family.run choices).Diverges
def Supported (family : CallFamily) : Prop := ∀ choices, (family.run choices).execution.Supported
def Equiv (left right : CallFamily) : Prop := ∀ a b, (left.run a).Equiv (right.run b)
def EquivReturn (left right : CallFamily) : Prop := ∀ a b, (left.run a).EquivReturn (right.run b)
def ReturnType (family : CallFamily) (kind : String) : Prop :=
  ∀ choices, (family.run choices).ReturnType kind

def deterministic (call : Call) : CallFamily := ⟨fun _ => call⟩

end CallFamily
end Mutable
end FormalSW.PyAst
