import Proof.Amplification.RecoveryMarkerCanonicalValues

/-! Canonical table parses identify the exact selected checker answer.
On flat requests, innerRows denotes the physically selected copy of the
certificate's outer table; the certificate codec remains unchanged. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerPayload
open LocalBitMultitape RecoveryMarkerHandoff
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def certificateAnswer (flat : Bool) (committed count payload : Nat) (table : FiniteValuation.Table)
    (innerRows outerRows : List Row) : Bool :=
  if flat then rootCheck (clausePredicate committed count table) innerRows payload
  else nestedCheck (clausePredicate committed count table) innerRows outerRows payload

theorem answer_certificate (marker : MarkerState) (x : CheckState) (words : Fin 3→List Bool)
    (word innerBits outerBits : List Bool) (table : FiniteValuation.Table) (rest : List Bool)
    (innerRows outerRows : List Row) (innerRest outerRest : List Bool)
    (hp : readList x.inner.base.extra.cap (readEntry x.inner.base.state.bits.length) word=some (table,rest))
    (hi : readMany (readRow x.inner.base.state.bits.length) x.innerTotal innerBits=some (innerRows,innerRest))
    (ho : readMany (readRow x.outer.data.outer.base.state.bits.length) x.outer.total outerBits=some (outerRows,outerRest)) :
    answer marker (output x words) word innerBits outerBits=
      certificateAnswer marker.outer.result (RadixSemantics.value (words 1)) (RadixSemantics.value (words 2))
        (RadixSemantics.value (words 0)) table innerRows outerRows := by
  have hpred := RecoveryNestedTable.valuation_predicate (output x words) word table rest hp
  cases hm : marker.outer.result
  · simp only [answer,certificateAnswer,hm,Bool.false_eq_true,ite_false]
    rw [RecoveryNestedTable.answer_eq_nestedCheck (output x words) word innerBits outerBits innerRows outerRows
      innerRest outerRest hi ho,hpred]
    rfl
  · simp only [answer,certificateAnswer,hm,ite_true]
    unfold RecoveryRowRoot.wholeAnswer
    change (readMany (readRow x.inner.base.state.bits.length) x.innerTotal innerBits).any
      (fun pair=>rootCheck (RecoveryRowStructure.tableLeafPredicate (output x words).inner word) pair.1
        (RadixSemantics.value (words 0)))=_
    rw [hi,Option.any_some]
    change rootCheck (RecoveryRowStructure.tableLeafPredicate (output x words).inner word) innerRows _=_
    rw [hpred]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryMarkerPayload
