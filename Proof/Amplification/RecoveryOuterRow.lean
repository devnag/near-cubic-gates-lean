import Proof.Amplification.RecoveryOuterRowAmbient

namespace NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def rowMachine := RecoveryGatedSequence.machine structuralMachine leafMachine 50
def rowCost (x : State) (bits : List Bool) := structureTime x.outer+leafCost (structured x bits)+2
def rowOutput (x : State) (bits innerBits : List Bool) :=
  if (structured x bits).outer.base.valid then leafOutput (structured x bits) innerBits else structured x bits

theorem structured_answer (x : State) (bits : List Bool) (rows : List Row) :
    answer (structured x bits) rows=leafCheck (predicate rows) (dataRow x.outer.base) := by
  have h := structure_retained x.outer bits
  unfold answer
  change (if RadixSemantics.value (structureOutput x.outer bits).base.kind=1 then
    predicate rows (RadixSemantics.value (structureOutput x.outer bits).base.state.bits) else true)=_
  rw [h.1,h.2.1]
  rfl

theorem row_run (x : State) (word outerBits innerBits : List Bool) (prior innerRows : List Row) (rest innerRest : List Bool)
    (hx : x.Valid word outerBits innerBits)
    (hw : x.outer.base.code.length=x.outer.base.state.bits.length)
    (hk : x.outer.base.kind.length=x.outer.base.state.bits.length)
    (hc : x.outer.base.count.length=x.outer.base.state.bits.length)
    (hp : readMany (readRow x.outer.bank.row.width) x.outer.total outerBits=some (prior,rest))
    (hprior : checkFrom [] prior=true)
    (hi : readMany (readRow x.inner.row.width) x.total innerBits=some (innerRows,innerRest)) :
    ∃ r,runFrom rowMachine (rowCost x outerBits) (x.cfg rowMachine.start)=some r ∧
      r.final=(rowOutput x outerBits innerBits).cfg r.final.control ∧ r.steps ≤ rowCost x outerBits ∧
      (rowOutput x outerBits innerBits).Valid word outerBits innerBits ∧
      (rowOutput x outerBits innerBits).outer.base.valid=
        (unpairCheck prior (dataRow x.outer.base) && leafCheck (predicate innerRows) (dataRow x.outer.base)) := by
  obtain ⟨first,hr0,hf0,hb0,hv0,ha0⟩ := structural_run x word outerBits innerBits prior rest hx hw hk hc hp hprior
  have hh0 : first.final.heads 50=0 := by rw [hf0]; rfl
  have ht0 : first.final.tapes 50=[(structured x outerBits).outer.base.valid] := by rw [hf0]; rfl
  cases ha : (structured x outerBits).outer.base.valid
  · rw [ha] at ht0
    obtain ⟨r,hr,hb,hf⟩ := RecoveryGatedSequence.reject_run structuralMachine leafMachine 50
      (structureTime x.outer) _ first hr0 hh0 ht0
    have hl : structureTime x.outer+1 ≤ rowCost x outerBits := by unfold rowCost; omega
    have hm := runFrom_moreFuel rowMachine _ (rowCost x outerBits-(structureTime x.outer+1)) _ r hr
    rw [Nat.add_sub_of_le hl] at hm
    refine ⟨r,hm,?_,hb.trans hl,?_,?_⟩
    · apply configuration_ext
      · rfl
      · rw [hf,hf0]; simp only [rowOutput,ha,Bool.false_eq_true,if_false]; rfl
      · rw [hf,hf0]; simp only [rowOutput,ha,Bool.false_eq_true,if_false]; rfl
    · simpa only [rowOutput,ha,Bool.false_eq_true,if_false] using hv0
    · simp only [rowOutput,ha,Bool.false_eq_true,if_false,←ha0,Bool.false_and]
  · have hflag : (structured x outerBits).outer.base.flags 1=decide (RadixSemantics.value (structured x outerBits).outer.base.kind=1) := by
      change (structureOutput x.outer outerBits).base.flags 1=decide (RadixSemantics.value (structureOutput x.outer outerBits).base.kind=1)
      rw [(structure_retained x.outer outerBits).2.1]
      exact structure_leaf_flag x.outer outerBits ha
    obtain ⟨last,hr1,hf1,hb1,hv1,ha1⟩ := leaf_run (structured x outerBits) word outerBits innerBits innerRows innerRest
      hv0 hi ha hflag
    have hnext : RecoveryCalls.restarted leafMachine first.final.heads first.final.tapes=(structured x outerBits).cfg leafMachine.start := by
      rw [hf0]; rfl
    rw [←hnext] at hr1
    rw [ha] at ht0
    obtain ⟨r,hr,hb,hf⟩ := RecoveryGatedSequence.accept_run structuralMachine leafMachine 50
      (structureTime x.outer) (leafCost (structured x outerBits)) _ first last hr0 hh0 ht0 hr1
    refine ⟨r,hr,?_,hb,?_,?_⟩
    · apply configuration_ext
      · rfl
      · rw [hf,hf1]; simp only [rowOutput,ha,if_true]; rfl
      · rw [hf,hf1]; simp only [rowOutput,ha,if_true]; rfl
    · simpa only [rowOutput,ha,if_true] using hv1
    · simp only [rowOutput,ha,if_true,←ha0,Bool.true_and]
      exact ha1.trans (structured_answer x outerBits innerRows)

end NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
