import lang.py.FormalSW.MachineRelocation

/-! Bounds for references retained by suspended execution. -/
namespace FormalSW.PyAst.HeapCalls.Relocation
open Mutable.Relocation
set_option Elab.async false

def EnvWithin (limit : Nat) (env : Env) : Prop :=
  ∀ name value, env name = some value → value.edge.Within limit

def SourceWithin (limit : Nat) : SequenceSource → Prop
  | .scalar _ => True
  | .ref address => address < limit

theorem relocateEnv_congr (left right : Nat → Nat) (limit : Nat) (env : Env)
    (agree : ∀ address < limit, left address = right address) (inside : EnvWithin limit env) :
    relocateEnv left env = relocateEnv right env := by
  funext name
  cases found : env name with
  | none => simp [relocateEnv, found]
  | some value =>
    simp only [relocateEnv, found, Option.map_some]
    exact congrArg some (relocateValue_congr left right limit value agree (inside name value found))

theorem relocateSource_congr (left right : Nat → Nat) (limit : Nat) (source : SequenceSource)
    (agree : ∀ address < limit, left address = right address) (inside : SourceWithin limit source) :
    relocateSource left source = relocateSource right source := by
  cases source with
  | scalar value => rfl
  | ref address => exact congrArg SequenceSource.ref (agree address inside)

/-- Only addresses are bounded; iterator positions may exceed the current sequence length. -/
def StmtWithin (limit : Nat) : Stmt → Prop
  | .classDef _ body => (∀ statement ∈ body, StmtWithin limit statement)
  | .functionDef _ _ _ body => (∀ statement ∈ body, StmtWithin limit statement)
  | .forIn _ _ body otherwise =>
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement)
  | .forDictionaryItems _ _ body otherwise =>
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement)
  | .dictionaryItemsStepLoop _ address keys _ body otherwise =>
      address < limit ∧
      (∀ source ∈ keys, SourceWithin limit source) ∧
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement)
  | .forZip _ _ body otherwise =>
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement)
  | .forReversed _ _ body otherwise =>
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement)
  | .reverseSequenceStepLoop _ source _ body otherwise =>
      SourceWithin limit source ∧
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement)
  | .zipStepLoop _ sources _ body otherwise =>
      (∀ source ∈ sources, SourceWithin limit source) ∧
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement)
  | .permutationStepLoop _ rows body otherwise =>
      (∀ row ∈ rows, ∀ source ∈ row, SourceWithin limit source) ∧
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement)
  | .rangeLoop _ _ _ body otherwise =>
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement)
  | .rangeStepLoop _ _ _ _ body otherwise =>
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement)
  | .sequenceStepLoop _ source _ body otherwise =>
      SourceWithin limit source ∧
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement)
  | .setStepLoop _ address _ _ body otherwise =>
      address < limit ∧
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement)
  | .unpackStepLoop _ source _ body otherwise =>
      SourceWithin limit source ∧
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement)
  | .enumerateStepLoop _ _ source _ _ body otherwise =>
      SourceWithin limit source ∧
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement)
  | .comprehensionAppend address _ => address < limit
  | .comprehensionAdd address _ => address < limit
  | .comprehensionStore address _ _ => address < limit
  | .ifThen _ yes no => (∀ statement ∈ yes, StmtWithin limit statement) ∧ (∀ statement ∈ no, StmtWithin limit statement)
  | .whileDo _ body otherwise =>
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement)
  | .loopResume loop => StmtWithin limit loop
  | _ => True

theorem relocateStmt_congr (left right : Nat → Nat) (limit : Nat) (statement : Stmt)
    (agree : ∀ address < limit, left address = right address) (inside : StmtWithin limit statement) :
    relocateStmt left statement = relocateStmt right statement := by
  have sourceSame (source : SequenceSource) (bounded : SourceWithin limit source) :=
    relocateSource_congr left right limit source agree bounded
  induction statement using Stmt.rec
    (motive_2 := fun statements => (∀ statement ∈ statements, StmtWithin limit statement) →
      statements.map (relocateStmt left) = statements.map (relocateStmt right)) <;>
    simp_all [StmtWithin, relocateStmt]
  intro row rowMember source sourceMember
  exact sourceSame source (inside.1 row rowMember source sourceMember)

def OperationWithin (limit : Nat) : Operation → Prop
  | .method receiver _ body =>
      receiver.edge.Within limit ∧
      (∀ statement ∈ body, StmtWithin limit statement)
  | .setField _ value =>
      value.edge.Within limit
  | .setItem value =>
      value.edge.Within limit
  | .setSlice value =>
      value.edge.Within limit
  | .append address =>
      address < limit
  | .pop address =>
      address < limit
  | .count address =>
      address < limit
  | .sort address =>
      address < limit
  | .sortReverse address =>
      address < limit
  | .add address =>
      address < limit
  | .dictionaryGet address =>
      address < limit
  | .dictionarySetDefault address =>
      address < limit
  | .dictionaryClear address =>
      address < limit
  | .comprehensionStore address =>
      address < limit
  | .sumGenerator _ _ env _ =>
      EnvWithin limit env
  | .comprehension _ _ env =>
      EnvWithin limit env
  | .comprehensionTargets _ _ env =>
      EnvWithin limit env
  | .setComprehension _ _ env =>
      EnvWithin limit env
  | .dictionaryComprehension _ _ _ env =>
      EnvWithin limit env
  | .permutationStart _ body otherwise following env =>
      EnvWithin limit env ∧
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement) ∧
      (∀ statement ∈ following, StmtWithin limit statement)
  | .combinationStart _ body otherwise following env =>
      EnvWithin limit env ∧
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement) ∧
      (∀ statement ∈ following, StmtWithin limit statement)
  | .zipStart _ body otherwise following env =>
      EnvWithin limit env ∧
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement) ∧
      (∀ statement ∈ following, StmtWithin limit statement)
  | .sumGeneratorTargets _ _ env _ =>
      EnvWithin limit env
  | .truthGenerator _ _ _ env =>
      EnvWithin limit env
  | .extremumGenerator _ _ _ _ env =>
      EnvWithin limit env
  | .generatorCollect _ _ _ env =>
      EnvWithin limit env
  | .nextGenerator _ _ _ env =>
      EnvWithin limit env
  | .isDigit receiver =>
      receiver.edge.Within limit
  | _ =>
      True

def SortWithin (limit : Nat) (cursor : SequenceSort) : Prop := EnvWithin limit cursor.env

def ExtremumWithin (limit : Nat) (cursor : SequenceExtremum) : Prop :=
  cursor.source.edge.Within limit ∧ EnvWithin limit cursor.env

def PairWithin (limit : Nat) (pair : Value × Value) : Prop :=
  pair.1.edge.Within limit ∧ pair.2.edge.Within limit

def FrameWithin (limit : Nat) : Frame → Prop
  | .sortedSource _ _ _ env =>
      EnvWithin limit env
  | .sortedReverse source _ _ env =>
      source.edge.Within limit ∧
      EnvWithin limit env
  | .sortedKey cursor candidate remaining keys =>
      candidate.edge.Within limit ∧
      SortWithin limit cursor ∧
      (∀ value ∈ remaining, value.edge.Within limit) ∧
      (∀ pair ∈ keys, PairWithin limit pair)
  | .extremumSource _ _ _ env =>
      EnvWithin limit env
  | .extremumKey cursor _ candidate best =>
      candidate.edge.Within limit ∧
      ExtremumWithin limit cursor ∧
      (∀ pair, best = some pair → PairWithin limit pair)
  | .dictionaryItemsReceiver _ body otherwise following env =>
      EnvWithin limit env ∧
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement) ∧
      (∀ statement ∈ following, StmtWithin limit statement)
  | .dictionaryValuesReceiver _ body otherwise following env =>
      EnvWithin limit env ∧
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement) ∧
      (∀ statement ∈ following, StmtWithin limit statement)
  | .dictionaryKey _ _ entries env =>
      EnvWithin limit env ∧
      (∀ entry ∈ entries, entry.2.edge.Within limit)
  | .dictionaryValue _ _ entries env =>
      EnvWithin limit env ∧
      (∀ entry ∈ entries, entry.2.edge.Within limit)
  | .sumStart loop env =>
      EnvWithin limit env ∧
      StmtWithin limit loop
  | .extremumStart _ loop env =>
      EnvWithin limit env ∧
      StmtWithin limit loop
  | .extremumResume original =>
      (∀ frame ∈ original, FrameWithin limit frame)
  | .generatorEnd =>
      True
  | .generatorConsumer _ =>
      True
  | .generatorReceiver _ _ env =>
      EnvWithin limit env
  | .initialized address =>
      address < limit
  | .attribute _ =>
      True
  | .methodReceiver _ _ env =>
      EnvWithin limit env
  | .assignAttribute _ _ rest env =>
      EnvWithin limit env ∧
      (∀ statement ∈ rest, StmtWithin limit statement)
  | .augmentAttribute _ _ _ rest env =>
      EnvWithin limit env ∧
      (∀ statement ∈ rest, StmtWithin limit statement)
  | .writeAttribute receiver _ rest env =>
      receiver.edge.Within limit ∧
      EnvWithin limit env ∧
      (∀ statement ∈ rest, StmtWithin limit statement)
  | .comprehensionResult address =>
      address < limit
  | .binaryLeft _ _ env _ =>
      EnvWithin limit env
  | .binaryRight _ left _ =>
      left.edge.Within limit
  | .compareLeft _ _ env =>
      EnvWithin limit env
  | .compareRight _ left =>
      left.edge.Within limit
  | .chainLeft _ _ _ env =>
      EnvWithin limit env
  | .chainRight _ left _ env =>
      left.edge.Within limit ∧
      EnvWithin limit env
  | .chainResult right _ env =>
      right.edge.Within limit ∧
      EnvWithin limit env
  | .unary _ =>
      True
  | .boolean _ _ env =>
      EnvWithin limit env
  | .conditional _ _ env =>
      EnvWithin limit env
  | .arguments operation done _ env =>
      EnvWithin limit env ∧
      OperationWithin limit operation ∧
      (∀ value ∈ done, value.edge.Within limit)
  | .starredArguments operation done _ env _ =>
      EnvWithin limit env ∧
      OperationWithin limit operation ∧
      (∀ value ∈ done, value.edge.Within limit)
  | .appendReceiver _ env =>
      EnvWithin limit env
  | .addReceiver _ env =>
      EnvWithin limit env
  | .assign _ rest env =>
      EnvWithin limit env ∧
      (∀ statement ∈ rest, StmtWithin limit statement)
  | .unpack _ rest env =>
      EnvWithin limit env ∧
      (∀ statement ∈ rest, StmtWithin limit statement)
  | .branch yes no rest env =>
      EnvWithin limit env ∧
      (∀ statement ∈ yes, StmtWithin limit statement) ∧
      (∀ statement ∈ no, StmtWithin limit statement) ∧
      (∀ statement ∈ rest, StmtWithin limit statement)
  | .discard rest env =>
      EnvWithin limit env ∧
      (∀ statement ∈ rest, StmtWithin limit statement)
  | .assertion _ rest env =>
      EnvWithin limit env ∧
      (∀ statement ∈ rest, StmtWithin limit statement)
  | .assertionMessage =>
      True
  | .reverseSequence _ body otherwise following env =>
      EnvWithin limit env ∧
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement) ∧
      (∀ statement ∈ following, StmtWithin limit statement)
  | .sequence _ body otherwise following env =>
      EnvWithin limit env ∧
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement) ∧
      (∀ statement ∈ following, StmtWithin limit statement)
  | .unpackSequence _ body otherwise following env =>
      EnvWithin limit env ∧
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement) ∧
      (∀ statement ∈ following, StmtWithin limit statement)
  | .enumerateSource _ _ _ body otherwise following env =>
      EnvWithin limit env ∧
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement) ∧
      (∀ statement ∈ following, StmtWithin limit statement)
  | .enumerateStart _ _ source body otherwise following env =>
      source.edge.Within limit ∧
      EnvWithin limit env ∧
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement) ∧
      (∀ statement ∈ following, StmtWithin limit statement)
  | .augmentItemReceiver _ _ _ rest env =>
      EnvWithin limit env ∧
      (∀ statement ∈ rest, StmtWithin limit statement)
  | .augmentItemIndex receiver _ _ rest env =>
      receiver.edge.Within limit ∧
      EnvWithin limit env ∧
      (∀ statement ∈ rest, StmtWithin limit statement)
  | .writeItem receiver index rest env =>
      receiver.edge.Within limit ∧
      index.edge.Within limit ∧
      EnvWithin limit env ∧
      (∀ statement ∈ rest, StmtWithin limit statement)
  | .assignItem _ _ rest env =>
      EnvWithin limit env ∧
      (∀ statement ∈ rest, StmtWithin limit statement)
  | .assignSlice _ _ _ _ rest env =>
      EnvWithin limit env ∧
      (∀ statement ∈ rest, StmtWithin limit statement)
  | .rangeArguments _ done _ body otherwise following env =>
      EnvWithin limit env ∧
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement) ∧
      (∀ statement ∈ following, StmtWithin limit statement) ∧
      (∀ value ∈ done, value.edge.Within limit)
  | .nextStart _ loop env =>
      EnvWithin limit env ∧
      StmtWithin limit loop

def WorkWithin (limit : Nat) : Work → Prop
  | .sortedLoop cursor remaining keys =>
      SortWithin limit cursor ∧
      (∀ value ∈ remaining, value.edge.Within limit) ∧
      (∀ pair ∈ keys, PairWithin limit pair)
  | .extremumLoop cursor _ best =>
      ExtremumWithin limit cursor ∧
      (∀ pair, best = some pair → PairWithin limit pair)
  | .dictionary _ entries env =>
      EnvWithin limit env ∧
      (∀ entry ∈ entries, entry.2.edge.Within limit)
  | .expr _ env =>
      EnvWithin limit env
  | .block body env =>
      EnvWithin limit env ∧
      (∀ statement ∈ body, StmtWithin limit statement)
  | .value value =>
      value.edge.Within limit
  | .operation operation values =>
      OperationWithin limit operation ∧
      (∀ value ∈ values, value.edge.Within limit)
  | .startRange _ values body otherwise following env =>
      EnvWithin limit env ∧
      (∀ statement ∈ body, StmtWithin limit statement) ∧
      (∀ statement ∈ otherwise, StmtWithin limit statement) ∧
      (∀ statement ∈ following, StmtWithin limit statement) ∧
      (∀ value ∈ values, value.edge.Within limit)

def StateWithin (state : State) : Prop :=
  WorkWithin state.heap.length state.work ∧ ∀ frame ∈ state.stack, FrameWithin state.heap.length frame

theorem relocateRuntimeOperation_congr (left right : Nat → Nat) (limit : Nat) (operation : Operation)
    (agree : ∀ address < limit, left address = right address) (inside : OperationWithin limit operation) :
    relocateRuntimeOperation left operation = relocateRuntimeOperation right operation := by
  have valueSame (value : Value) (bounded : value.edge.Within limit) := relocateValue_congr left right limit value agree bounded
  have envSame (env : Env) (bounded : EnvWithin limit env) := relocateEnv_congr left right limit env agree bounded
  have stmtSame (stmt : Stmt) (bounded : StmtWithin limit stmt) := relocateStmt_congr left right limit stmt agree bounded
  cases operation <;> simp_all [OperationWithin, relocateRuntimeOperation, relocateOperation]

theorem relocateSort_congr (left right : Nat → Nat) (limit : Nat) (cursor : SequenceSort)
    (agree : ∀ address < limit, left address = right address) (inside : SortWithin limit cursor) :
    relocateSort left cursor = relocateSort right cursor := by
  simp only [relocateSort, relocateEnv_congr left right limit cursor.env agree inside]

theorem relocateExtremum_congr (left right : Nat → Nat) (limit : Nat) (cursor : SequenceExtremum)
    (agree : ∀ address < limit, left address = right address) (inside : ExtremumWithin limit cursor) :
    relocateExtremum left cursor = relocateExtremum right cursor := by
  simp only [relocateExtremum, relocateValue_congr left right limit cursor.source agree inside.1,
    relocateEnv_congr left right limit cursor.env agree inside.2]

theorem relocatePair_congr (left right : Nat → Nat) (limit : Nat) (pair : Value × Value)
    (agree : ∀ address < limit, left address = right address) (inside : PairWithin limit pair) :
    relocatePair left pair = relocatePair right pair := by
  simp only [relocatePair, relocateValue_congr left right limit pair.1 agree inside.1,
    relocateValue_congr left right limit pair.2 agree inside.2]

theorem relocateBest_congr (left right : Nat → Nat) (limit : Nat) (best : Option (Value × Value))
    (agree : ∀ address < limit, left address = right address)
    (inside : ∀ pair, best = some pair → PairWithin limit pair) :
    best.map (relocatePair left) = best.map (relocatePair right) := by
  cases best with
  | none => rfl
  | some pair => exact congrArg some (relocatePair_congr left right limit pair agree (inside pair rfl))

theorem relocateFrame_congr (left right : Nat → Nat) (limit : Nat) (frame : Frame)
    (agree : ∀ address < limit, left address = right address) (inside : FrameWithin limit frame) :
    relocateFrame left frame = relocateFrame right frame := by
  have valueSame (value : Value) (bounded : value.edge.Within limit) := relocateValue_congr left right limit value agree bounded
  have envSame (env : Env) (bounded : EnvWithin limit env) := relocateEnv_congr left right limit env agree bounded
  have stmtSame (stmt : Stmt) (bounded : StmtWithin limit stmt) := relocateStmt_congr left right limit stmt agree bounded
  have opSame (op : Operation) (bounded : OperationWithin limit op) := relocateRuntimeOperation_congr left right limit op agree bounded
  have sortSame (cursor : SequenceSort) (bounded : SortWithin limit cursor) := relocateSort_congr left right limit cursor agree bounded
  have extremumSame (cursor : SequenceExtremum) (bounded : ExtremumWithin limit cursor) := relocateExtremum_congr left right limit cursor agree bounded
  have pairSame (pair : Value × Value) (bounded : PairWithin limit pair) := relocatePair_congr left right limit pair agree bounded
  have bestSame (best : Option (Value × Value)) (bounded : ∀ pair, best = some pair → PairWithin limit pair) :=
    relocateBest_congr left right limit best agree bounded
  induction frame using Frame.rec
    (motive_2 := fun frames => (∀ frame ∈ frames, FrameWithin limit frame) →
      frames.map (relocateFrame left) = frames.map (relocateFrame right)) <;>
    simp_all [FrameWithin, relocateFrame]
  all_goals
    intro key value member
    exact valueSame value (inside.2 key value member)

theorem relocateWork_congr (left right : Nat → Nat) (limit : Nat) (work : Work)
    (agree : ∀ address < limit, left address = right address) (inside : WorkWithin limit work) :
    relocateWork left work = relocateWork right work := by
  have valueSame (value : Value) (bounded : value.edge.Within limit) := relocateValue_congr left right limit value agree bounded
  have envSame (env : Env) (bounded : EnvWithin limit env) := relocateEnv_congr left right limit env agree bounded
  have stmtSame (stmt : Stmt) (bounded : StmtWithin limit stmt) := relocateStmt_congr left right limit stmt agree bounded
  have opSame (op : Operation) (bounded : OperationWithin limit op) := relocateRuntimeOperation_congr left right limit op agree bounded
  have sortSame (cursor : SequenceSort) (bounded : SortWithin limit cursor) := relocateSort_congr left right limit cursor agree bounded
  have extremumSame (cursor : SequenceExtremum) (bounded : ExtremumWithin limit cursor) := relocateExtremum_congr left right limit cursor agree bounded
  have pairSame (pair : Value × Value) (bounded : PairWithin limit pair) := relocatePair_congr left right limit pair agree bounded
  have bestSame (best : Option (Value × Value)) (bounded : ∀ pair, best = some pair → PairWithin limit pair) :=
    relocateBest_congr left right limit best agree bounded
  cases work <;> simp_all [WorkWithin, relocateWork]
  intro key value member
  exact valueSame value (inside.2 key value member)

theorem relocateState_congr (left right : Nat → Nat) (logical : State) (physical : Mutable.Heap)
    (agree : ∀ address < logical.heap.length, left address = right address) (inside : StateWithin logical) :
    relocateState left physical logical = relocateState right physical logical := by
  have work := relocateWork_congr left right logical.heap.length logical.work agree inside.1
  have stack := List.map_congr_left (fun frame member =>
    relocateFrame_congr left right logical.heap.length frame agree (inside.2 frame member))
  simp only [relocateState, work, stack]

theorem valueWithin_mono (before after : Nat) (value : Value)
    (larger : before ≤ after) (inside : value.edge.Within before) : value.edge.Within after := by
  cases value with
  | scalar value => trivial
  | ref address => exact Nat.lt_of_lt_of_le inside larger

theorem EnvWithin.mono {before after : Nat} {env : Env}
    (inside : EnvWithin before env) (larger : before ≤ after) : EnvWithin after env := by
  intro name value found
  exact valueWithin_mono before after value larger (inside name value found)

theorem SourceWithin.mono {before after : Nat} {source : SequenceSource}
    (inside : SourceWithin before source) (larger : before ≤ after) : SourceWithin after source := by
  cases source with
  | scalar value => trivial
  | ref address => exact Nat.lt_of_lt_of_le inside larger

theorem StmtWithin.mono {before after : Nat} {statement : Stmt}
    (inside : StmtWithin before statement) (larger : before ≤ after) : StmtWithin after statement := by
  have addressLarger (address : Nat) (bounded : address < before) := Nat.lt_of_lt_of_le bounded larger
  have sourceLarger (source : SequenceSource) (bounded : SourceWithin before source) := bounded.mono larger
  induction statement using Stmt.rec
    (motive_2 := fun statements => (∀ statement ∈ statements, StmtWithin before statement) →
      ∀ statement ∈ statements, StmtWithin after statement) <;> simp_all [StmtWithin]
  case permutationStepLoop =>
    intro row rowMember source sourceMember
    exact sourceLarger source (inside.1 row rowMember source sourceMember)
  case cons =>
    rename_i head tail current first rest old member
    rcases member with rfl | member
    · exact first
    · exact rest current member

theorem OperationWithin.mono {before after : Nat} {operation : Operation}
    (inside : OperationWithin before operation) (larger : before ≤ after) : OperationWithin after operation := by
  have addressLarger (address : Nat) (bounded : address < before) := Nat.lt_of_lt_of_le bounded larger
  have valueLarger (value : Value) (bounded : value.edge.Within before) := valueWithin_mono before after value larger bounded
  have envLarger (env : Env) (bounded : EnvWithin before env) := bounded.mono larger
  have stmtLarger (stmt : Stmt) (bounded : StmtWithin before stmt) := bounded.mono larger
  cases operation <;> simp_all [OperationWithin]

theorem SortWithin.mono {before after : Nat} {cursor : SequenceSort}
    (inside : SortWithin before cursor) (larger : before ≤ after) : SortWithin after cursor :=
  EnvWithin.mono inside larger

theorem ExtremumWithin.mono {before after : Nat} {cursor : SequenceExtremum}
    (inside : ExtremumWithin before cursor) (larger : before ≤ after) : ExtremumWithin after cursor :=
  ⟨valueWithin_mono before after cursor.source larger inside.1, inside.2.mono larger⟩

theorem PairWithin.mono {before after : Nat} {pair : Value × Value}
    (inside : PairWithin before pair) (larger : before ≤ after) : PairWithin after pair :=
  ⟨valueWithin_mono before after pair.1 larger inside.1, valueWithin_mono before after pair.2 larger inside.2⟩

theorem FrameWithin.mono {before after : Nat} {frame : Frame}
    (inside : FrameWithin before frame) (larger : before ≤ after) : FrameWithin after frame := by
  have addressLarger (address : Nat) (bounded : address < before) := Nat.lt_of_lt_of_le bounded larger
  have valueLarger (value : Value) (bounded : value.edge.Within before) := valueWithin_mono before after value larger bounded
  have envLarger (env : Env) (bounded : EnvWithin before env) := bounded.mono larger
  have stmtLarger (stmt : Stmt) (bounded : StmtWithin before stmt) := bounded.mono larger
  have opLarger (op : Operation) (bounded : OperationWithin before op) := bounded.mono larger
  have sortLarger (cursor : SequenceSort) (bounded : SortWithin before cursor) := bounded.mono larger
  have extremumLarger (cursor : SequenceExtremum) (bounded : ExtremumWithin before cursor) := bounded.mono larger
  have pairLarger (pair : Value × Value) (bounded : PairWithin before pair) := bounded.mono larger
  induction frame using Frame.rec
    (motive_2 := fun frames => (∀ frame ∈ frames, FrameWithin before frame) →
      ∀ frame ∈ frames, FrameWithin after frame) <;> simp_all [FrameWithin]
  case dictionaryKey | dictionaryValue =>
    intro key value member
    exact valueLarger value (inside.2 key value member)
  case cons =>
    rename_i head tail current first rest old member
    rcases member with rfl | member
    · exact first
    · exact rest current member

theorem WorkWithin.mono {before after : Nat} {work : Work}
    (inside : WorkWithin before work) (larger : before ≤ after) : WorkWithin after work := by
  have valueLarger (value : Value) (bounded : value.edge.Within before) := valueWithin_mono before after value larger bounded
  have envLarger (env : Env) (bounded : EnvWithin before env) := bounded.mono larger
  have stmtLarger (stmt : Stmt) (bounded : StmtWithin before stmt) := bounded.mono larger
  have opLarger (op : Operation) (bounded : OperationWithin before op) := bounded.mono larger
  have sortLarger (cursor : SequenceSort) (bounded : SortWithin before cursor) := bounded.mono larger
  have extremumLarger (cursor : SequenceExtremum) (bounded : ExtremumWithin before cursor) := bounded.mono larger
  have pairLarger (pair : Value × Value) (bounded : PairWithin before pair) := bounded.mono larger
  cases work <;> simp_all [WorkWithin]
  intro key value member
  exact valueLarger value (inside.2 key value member)

def GlobalsWithin (limit : Nat) (globals : Mutable.Globals) : Prop :=
  ∀ entry ∈ globals, entry.2.edge.Within limit

theorem relocateGlobals_congr (left right : Nat → Nat) (limit : Nat) (globals : Mutable.Globals)
    (agree : ∀ address < limit, left address = right address) (inside : GlobalsWithin limit globals) :
    relocateGlobals left globals = relocateGlobals right globals := by
  apply List.map_congr_left
  intro entry member
  exact congrArg (fun value => (entry.1, value)) (relocateValue_congr left right limit entry.2 agree (inside entry member))

theorem GlobalsWithin.mono {before after : Nat} {globals : Mutable.Globals}
    (inside : GlobalsWithin before globals) (larger : before ≤ after) : GlobalsWithin after globals := by
  intro entry member
  exact valueWithin_mono before after entry.2 larger (inside entry member)

theorem relocateStack_congr (left right : Nat → Nat) (limit : Nat) (stack : List Frame)
    (agree : ∀ address < limit, left address = right address) (inside : ∀ frame ∈ stack, FrameWithin limit frame) :
    stack.map (relocateFrame left) = stack.map (relocateFrame right) :=
  List.map_congr_left (fun frame member => relocateFrame_congr left right limit frame agree (inside frame member))

theorem EnvWithin.setLocal {limit : Nat} {env : Env} (inside : EnvWithin limit env)
    (name : String) (value : Value) (valueInside : value.edge.Within limit) :
    EnvWithin limit (setLocal env name value) := by
  intro query stored found
  by_cases same : query = name
  · have equal : value = stored := by simpa [HeapCalls.setLocal, same] using found
    exact equal ▸ valueInside
  · exact inside query stored (by simpa [HeapCalls.setLocal, same] using found)

theorem StateWithin.assign (heap : Mutable.Heap) (value : Value) (name : String) (body : List Stmt)
    (env : Env) (stack : List Frame)
    (inside : StateWithin ⟨.value value, .assign name body env :: stack, heap⟩) :
    StateWithin ⟨.block body (setLocal env name value), stack, heap⟩ := by
  have saved := inside.2 (.assign name body env) (by simp)
  simp only [FrameWithin] at saved
  refine ⟨⟨saved.1.setLocal name value inside.1, saved.2⟩, ?_⟩
  intro frame member
  exact inside.2 frame (by simp [member])

theorem argumentsState_within (heap : Mutable.Heap) (operation : Operation) (env : Env)
    (done : List Value) (expressions : List Expr) (stack : List Frame)
    (operationInside : OperationWithin heap.length operation) (envInside : EnvWithin heap.length env)
    (doneInside : ∀ value ∈ done, value.edge.Within heap.length)
    (stackInside : ∀ frame ∈ stack, FrameWithin heap.length frame) :
    StateWithin (argumentsState operation env done expressions stack heap) := by
  cases expressions with
  | nil => exact ⟨⟨operationInside, doneInside⟩, stackInside⟩
  | cons head tail =>
    refine ⟨envInside, ?_⟩
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [FrameWithin] using And.intro envInside (And.intro operationInside doneInside)
    · exact stackInside frame member

theorem StateWithin.arguments (heap : Mutable.Heap) (value : Value) (operation : Operation)
    (done : List Value) (rest : List Expr) (env : Env) (stack : List Frame)
    (inside : StateWithin ⟨.value value, .arguments operation done rest env :: stack, heap⟩) :
    StateWithin (argumentsState operation env (done ++ [value]) rest stack heap) := by
  have saved := inside.2 (.arguments operation done rest env) (by simp)
  simp only [FrameWithin] at saved
  apply argumentsState_within heap operation env _ rest stack saved.2.1 saved.1
  · intro item member
    rcases List.mem_append.mp member with old | fresh
    · exact saved.2.2 item old
    · simpa only [List.mem_singleton.mp fresh] using inside.1
  · intro frame member
    exact inside.2 frame (by simp [member])

end FormalSW.PyAst.HeapCalls.Relocation
