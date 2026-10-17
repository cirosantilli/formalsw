import FormalSW

namespace tests.py.builtinModels

open FormalSW.Py.Builtin

example : Int.floorDiv (-3) 2 = .ok (-2) := rfl
example : Int.mod 3 (-2) = .ok (-1) := rfl
example : Int.powMod 3 (-1) 11 = .ok 4 := rfl
example : Int.parse [32, 45, 48, 120, 102, 102, 32] 0 = .ok (-255) := rfl
example : Int.bitAnd (-5) 3 = 3 := rfl
example : Int.bitOr (-5) 3 = -5 := rfl
example : Int.toBytes (-1024) 2 .big true = .ok [252, 0] := rfl
example : Int.fromBytes [252, 0] .big true = -1024 := rfl
example : Function.Numeric.round 25 (some (-1)) = .ok 20 := rfl
example : Function.Numeric.round 35 (some (-1)) = .ok 40 := rfl

example : Slice.indexList { step := some (-1) } 4 = .ok [3, 2, 1, 0] := rfl
example : Range.toList ⟨3, -1, -1⟩ = [3, 2, 1, 0] := rfl
example : Range.equivalent ⟨0, 0, 1⟩ ⟨2, 1, 3⟩ = true := rfl

def orderedDict : Dict.Dict Nat String :=
  Dict.set (Dict.set (Dict.set Dict.empty 2 "two") 1 "one") 2 "TWO"

example : Dict.keys orderedDict = [2, 1] := by native_decide
example : Dict.values orderedDict = ["TWO", "one"] := by native_decide
example : (letI : Ord Nat := inferInstance; orderedDict.tree.inner.inner.WF) :=
  Dict.tree_wellFormed orderedDict

def leftSet : Set.Set Nat := Set.ofList [1, 2, 3]
def rightSet : Set.Set Nat := Set.ofList [3, 4]

example : Set.toList (Set.intersection leftSet rightSet) = [3] := by native_decide
example : Set.toList (Set.symmetricDifference leftSet rightSet) = [1, 2, 4] := by native_decide
example : (letI : Ord Nat := inferInstance; leftSet.inner.inner.inner.WF) :=
  Set.tree_wellFormed leftSet

example : Bytes.fromHex "00 0f FF" = .ok [0, 15, 255] := rfl
example : Bytes.zfill [45, 52, 50] 5 = [45, 48, 48, 52, 50] := rfl
example : Subsequence.replace [1, 2] [] [0] 2 = [0, 1, 0, 2] := rfl
example : Str.chr 0x10ffff = .ok [0x10ffff] := rfl
example : Str.chr 0x110000 = .error (.valueError "chr() arg not in range(0x110000)") := by
  rfl

example : Function.Iterable.zip [[1], [2, 3]] true =
    .error (.valueError "zip() arguments have different lengths") := rfl

def releasedView := MemoryView.release (MemoryView.create 7 [1, 2])
example : MemoryView.toBytes releasedView =
    .error (.valueError "operation forbidden on released memoryview object") := rfl

end tests.py.builtinModels
