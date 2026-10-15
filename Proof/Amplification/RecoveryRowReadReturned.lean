import Proof.Amplification.RecoveryRowTableAdvance

/-! The successful row returns the exact source cursor and valuation
parameters needed by the next table iteration. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev ReadLeafResult (x : Children) (word bits input : List Bool) :=
  RecoveryRowLeaf.LeafResult (structureOutput (readChildren x input) bits).base.state
    (structureOutput (readChildren x input) bits).base.extra (structureOutput (readChildren x input) bits).base.kind word
def readFinished (x : Children) (word bits input : List Bool) (out : ReadLeafResult x word bits input) :=
  leafFinished (structureOutput (readChildren x input) bits) word out

theorem read_finished_retained (x : Children) (word bits input : List Bool) (out : ReadLeafResult x word bits input)
    (hi : 4*x.base.state.bits.length ≤ input.length) :
    (readFinished x word bits input out).base.source=x.base.source ∧
    (readFinished x word bits input out).base.pos=x.base.pos+8*x.base.state.bits.length ∧
    (readFinished x word bits input out).total=x.total ∧
    (readFinished x word bits input out).copyCapacity=x.copyCapacity ∧
    (readFinished x word bits input out).lookupCapacity=x.lookupCapacity ∧
    (readFinished x word bits input out).base.state.bits.length=x.base.state.bits.length ∧
    (readFinished x word bits input out).base.extra.binaryCount=x.base.extra.binaryCount ∧
    (readFinished x word bits input out).base.extra.committed=x.base.extra.committed ∧
    (readFinished x word bits input out).base.extra.cap=x.base.extra.cap := by
  have h := structure_retained (readChildren x input) bits
  refine ⟨h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2,?_,?_,?_,?_⟩
  · exact out.width.trans ((congrArg List.length h.1).trans (afterRead_width x.base input hi))
  · exact out.count.trans (congrArg RecoveryClauseEvaluation.Extra.binaryCount h.2.2.1)
  · exact out.committed.trans (congrArg RecoveryClauseEvaluation.Extra.committed h.2.2.1)
  · exact out.cap.trans (congrArg RecoveryClauseEvaluation.Extra.cap h.2.2.1)

theorem read_finished_source (x : Children) (word bits pre input : List Bool)
    (out : ReadLeafResult x word bits input) (hi : 4*x.base.state.bits.length ≤ input.length)
    (hs : x.base.source=pre++frame input) (hp : x.base.pos=pre.length) :
    ∃ nextPre,(readFinished x word bits input out).base.source=
        nextPre++frame (input.drop (4*x.base.state.bits.length)) ∧
      (readFinished x word bits input out).base.pos=nextPre.length := by
  have h := read_finished_retained x word bits input out hi
  refine ⟨pre++Streaming.marks (input.take (4*x.base.state.bits.length)),?_,?_⟩
  · rw [h.1,List.append_assoc,←Streaming.frame_append,List.take_append_drop]
    exact hs
  · rw [h.2.1,hp]
    simp only [List.length_append,Streaming.marks_length,List.length_take,Nat.min_eq_left hi]
    omega

theorem dataRow_afterRead (x : Children) (input : List Bool) :
    dataRow (readChildren x input).base=RecoveryRowFields.parsed x.base.state.bits.length input := rfl

def tableLeafPredicate (x : Children) (word : List Bool) (code : Nat) : Bool :=
  (readList x.base.extra.cap (readEntry x.base.state.bits.length) word).any (fun pair=>
    RepairSource.RecoveryOracle.CompactCertificate.clausePredicate
      (RadixSemantics.value x.base.extra.committed) (RadixSemantics.value x.base.extra.binaryCount) pair.1 code)

theorem read_leaf_predicate (x : Children) (word input : List Bool)
    (hi : 4*x.base.state.bits.length ≤ input.length) :
    leafAnswer (readChildren x input) word=
      leafCheck (tableLeafPredicate x word) (RecoveryRowFields.parsed x.base.state.bits.length input) := by
  unfold leafAnswer RecoveryRowLeaf.leafWordCheck RecoveryClauseEvaluation.clauseWordCheck leafCheck tableLeafPredicate
  change (if RadixSemantics.value (RecoveryRowFields.words x.base.state.bits.length input 0)=1 then
    (readList x.base.extra.cap (readEntry (x.base.afterRead input).state.bits.length) word).any _ else true)=_
  rw [afterRead_width x.base input hi]
  rfl

theorem read_whole_answer (x : Children) (word bits input : List Bool) (rows : List Row) (rest : List Bool)
    (hp : readMany (readRow x.bank.row.width) x.total bits=some (rows,rest))
    (hrows : checkFrom [] rows=true) (hi : 4*x.base.state.bits.length ≤ input.length) :
    readWholeAnswer x word bits input=
      (unpairCheck rows (RecoveryRowFields.parsed x.base.state.bits.length input) &&
        leafCheck (tableLeafPredicate x word) (RecoveryRowFields.parsed x.base.state.bits.length input)) := by
  unfold readWholeAnswer
  rw [RecoveryCertificateRow.row_isSome,show decide (4*x.base.state.bits.length ≤ input.length)=true by simp [hi]]
  simp only [Bool.true_and]
  rw [whole_row_answer (readChildren x input) word bits rows rest hp hrows,dataRow_afterRead,
    read_leaf_predicate x word input hi]

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
