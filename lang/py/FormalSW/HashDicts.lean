import lang.py.FormalSW.HashKeys

/-! Ordered dictionaries retain the first equal key and the current shared value. -/
namespace FormalSW.PyAst.HashDict

abbrev Entry (α : Type) := HashKey × α × α

def find? (entries : List (Entry α)) (key : HashKey) : Option (Entry α) :=
  entries.find? (fun entry => HashKey.equal entry.1 key)

def lookup (entries : List (Entry α)) (key : HashKey) : Option α :=
  (find? entries key).map (fun entry => entry.2.2)

/-- Updating an equal key retains its representative and insertion position. -/
def insert : List (Entry α) → HashKey → α → α → List (Entry α)
  | [], key, original, value => [(key, original, value)]
  | entry :: rest, key, original, value =>
      if HashKey.equal entry.1 key then (entry.1, entry.2.1, value) :: rest
      else entry :: insert rest key original value

end FormalSW.PyAst.HashDict
