import Proof.Amplification.RecoveryNestedTableState

namespace NearCubicWires.RepairOrdinary.RecoveryNestedTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
open RepairSource.RecoveryOracle.CompactCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem inner_accepted (x : State) (word bits : List Bool)
    (ha : innerAnswer x word bits=true) :
    ∃ rows rest,readMany (readRow x.inner.base.state.bits.length) x.innerTotal bits=some (rows,rest) ∧
      checkFrom [] rows=true ∧ rows.all (leafCheck (tableLeafPredicate x.inner word))=true := by
  simp only [innerAnswer,Option.any_eq_true] at ha
  obtain ⟨⟨rows,rest⟩,hp,hc⟩ := ha
  rw [Bool.and_eq_true] at hc
  exact ⟨rows,rest,hp,hc.1,hc.2⟩

theorem answer_of_inner (x : State) (word innerBits outerBits : List Bool) (rows : List Row) (rest : List Bool)
    (hp : readMany (readRow x.inner.base.state.bits.length) x.innerTotal innerBits=some (rows,rest))
    (ha : innerAnswer x word innerBits=true) :
    answer x word innerBits outerBits=RecoveryOuterRoot.wholeAnswer x.outer rows outerBits := by
  simp only [innerAnswer,hp,Option.any_some] at ha
  simp only [answer,hp,Option.any_some,ha,Bool.true_and]

theorem inner_answer_and (x : State) (word innerBits outerBits : List Bool) :
    (innerAnswer x word innerBits && answer x word innerBits outerBits)=answer x word innerBits outerBits := by
  unfold innerAnswer answer
  cases hp : readMany (readRow x.inner.base.state.bits.length) x.innerTotal innerBits with
  | none => rfl
  | some pair =>
    simp only [Option.any_some]
    cases (checkFrom [] pair.1 && pair.1.all (leafCheck (tableLeafPredicate x.inner word))) <;> rfl

theorem predicate_hasRoot (rows : List Row) : RecoveryOuterLeaf.predicate rows=hasRoot rows := by
  funext code
  apply congrArg (fun f : Row → Bool=>rows.any f)
  funext row
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq,beq_iff_eq]
  exact eq_comm

theorem answer_sound (x : State) (word innerBits outerBits : List Bool)
    (ha : answer x word innerBits outerBits=true) :
    ∃ codes,BalancedCNFSATEncoding.decodeNestedBalancedCNFPayload (RadixSemantics.value x.outer.key)=some codes ∧
      codes.all (tableLeafPredicate x.inner word)=true := by
  simp only [answer,Option.any_eq_true,Bool.and_eq_true] at ha
  obtain ⟨⟨inner,innerRest⟩,_,hi,ho⟩ := ha
  simp only [RecoveryOuterRoot.wholeAnswer,Option.any_eq_true] at ho
  obtain ⟨⟨outer,outerRest⟩,_,hroot⟩ := ho
  rw [predicate_hasRoot] at hroot
  apply (nestedCheck_iff (tableLeafPredicate x.inner word) (RadixSemantics.value x.outer.key)).mp
  exact ⟨inner,outer,by simpa only [nestedCheck,Bool.and_eq_true] using And.intro hi hroot⟩

end NearCubicWires.RepairOrdinary.RecoveryNestedTable
