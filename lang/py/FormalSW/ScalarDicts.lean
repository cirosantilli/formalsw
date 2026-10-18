import lang.py.FormalSW.ScalarSets

/-! Insertion-ordered dictionaries with builtin scalar keys and arbitrary values.
Equal numeric keys share an entry; replacement retains its first key and position. -/
namespace FormalSW.PyAst.ScalarDict

def lookup (entries : List (Constant × α)) (key : Constant) : Option α :=
  match entries with
  | [] => none
  | (stored, value) :: rest =>
      if (scalarCompare .eq stored key).getD false then some value else lookup rest key

def insert (entries : List (Constant × α)) (key : Constant) (value : α) : List (Constant × α) :=
  match entries with
  | [] => [(key, value)]
  | (stored, previous) :: rest =>
      if (scalarCompare .eq stored key).getD false then (stored, value) :: rest
      else (stored, previous) :: insert rest key value

def Valid (entries : List (Constant × α)) : Prop :=
  ScalarSet.Valid (entries.map Prod.fst)

theorem lookup_insert_self (entries : List (Constant × α)) (key : Constant) (value : α) :
    lookup (insert entries key value) key = some value := by
  have reflexive : scalarCompare .eq key key = some true := by
    cases key <;> simp [scalarCompare, evalCmpOp]
  induction entries with
  | nil => simp [insert, lookup, reflexive]
  | cons entry rest ih =>
      obtain ⟨stored, previous⟩ := entry
      simp only [insert]
      split <;> simp_all [lookup]

end FormalSW.PyAst.ScalarDict
