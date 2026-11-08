import lang.py.FormalSW.HeapRuntimeCostSorting
import lang.py.FormalSW.HeapSortingCalls
import lang.py.FormalSW.StringListWork

namespace FormalSW.PyAst.HeapCalls.Runtime

/-- Sort a scalar string list with the existing comparison-sort tariff,
retaining the input heap and charging the fresh result list. -/
theorem EvaluatesIn.sorted_strings
    (source : EvaluatesIn arithmetic module env expression heap ca (.ref address) middle)
    (found : middle[address]? = some (.list (StringList.encode names))) :
    EvaluatesIn arithmetic module env (.builtinCall .sorted [expression]) heap
      (ca + SortWork.sorting arithmetic (names.map Constant.string) + names.length + 3)
      (.ref middle.length) (middle ++ [.list (StringList.encode (ScalarSort.strings names))]) := by
  have sorted : primitive (.builtin .sorted) [.ref address] middle =
      some (.ok (.ref middle.length), middle ++ [.list (StringList.encode (ScalarSort.strings names))]) := by
    have evaluated := primitive_sorted_list middle address (names.map Constant.string)
      ((ScalarSort.strings names).map Constant.string)
      (by simpa only [StringList.encode, List.map_map] using found) (ScalarSort.sort_strings names)
    simpa only [StringList.encode, List.map_map] using evaluated
  have priced : operation arithmetic middle (.builtin .sorted) [.ref address] =
      some (SortWork.sorting arithmetic (names.map Constant.string)) := by
    simp only [operation, SortWork.operation, found]
    have scalars := SortWork.scalars_map (names.map Constant.string)
    simpa only [StringList.encode, List.map_map] using
      congrArg (Option.map (SortWork.sorting arithmetic)) scalars
  have run := EvaluatesIn.sorted source sorted priced
  simpa only [StringList.encode, List.length_map, (ScalarSort.strings_perm names).length_eq] using run

end FormalSW.PyAst.HeapCalls.Runtime
