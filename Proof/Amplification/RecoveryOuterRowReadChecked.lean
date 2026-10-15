import Proof.Amplification.RecoveryOuterRowRead

namespace NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def readRowMachine := RecoveryGatedSequence.machine readMachine rowMachine 50
def readRowCost (x : State) (outerBits input : List Bool) :=
  RecoveryRowFields.budget x.outer.base.state.bits.length+rowCost (readState x input) outerBits+2
def readRowOutput (x : State) (outerBits innerBits input : List Bool) := rowOutput (readState x input) outerBits innerBits
def readRowAnswer (x : State) (outerBits innerBits input : List Bool) :=
  (readRow x.outer.base.state.bits.length input).isSome && (readRowOutput x outerBits innerBits input).outer.base.valid

theorem read_row_run (x : State) (word outerBits innerBits pre input : List Bool)
    (prior innerRows : List Row) (rest innerRest : List Bool)
    (hx : x.Valid word outerBits innerBits)
    (hs : x.outer.base.source=pre++frame input) (hpos : x.outer.base.pos=pre.length)
    (hp : readMany (readRow x.outer.bank.row.width) x.outer.total outerBits=some (prior,rest))
    (hprior : checkFrom [] prior=true)
    (hi : readMany (readRow x.inner.row.width) x.total innerBits=some (innerRows,innerRest)) :
    ∃ r,runFrom readRowMachine (readRowCost x outerBits input) (x.cfg readRowMachine.start)=some r ∧
      r.steps ≤ readRowCost x outerBits input ∧ r.final.heads 50=0 ∧
      r.final.tapes 50=[readRowAnswer x outerBits innerBits input] ∧
      ((readRow x.outer.base.state.bits.length input).isSome=true →
        r.final=(readRowOutput x outerBits innerBits input).cfg r.final.control ∧
        (readRowOutput x outerBits innerBits input).Valid word outerBits innerBits ∧
        (readRowOutput x outerBits innerBits input).outer.base.valid=
          (unpairCheck prior (RecoveryRowFields.parsed x.outer.base.state.bits.length input) &&
            leafCheck (predicate innerRows) (RecoveryRowFields.parsed x.outer.base.state.bits.length input))) := by
  obtain ⟨first,hr0,hb0,hh0,ht0,hout0⟩ := read_run x word pre input hx.1.1 hs hpos
  cases ha : (readRow x.outer.base.state.bits.length input).isSome
  · rw [ha] at ht0
    obtain ⟨r,hr,hb,hf⟩ := RecoveryGatedSequence.reject_run readMachine rowMachine 50
      (RecoveryRowFields.budget x.outer.base.state.bits.length) _ first hr0 hh0 ht0
    have hl : RecoveryRowFields.budget x.outer.base.state.bits.length+1 ≤ readRowCost x outerBits input := by
      unfold readRowCost; omega
    have hm := runFrom_moreFuel readRowMachine _ (readRowCost x outerBits input-
      (RecoveryRowFields.budget x.outer.base.state.bits.length+1)) _ r hr
    rw [Nat.add_sub_of_le hl] at hm
    refine ⟨r,hm,hb.trans hl,?_,?_,?_⟩
    · rw [hf]; exact hh0
    · rw [hf]; change first.final.tapes 50=_
      simp only [ht0,readRowAnswer,ha,Bool.false_and]
    · simp only [Bool.false_eq_true,IsEmpty.forall_iff]
  · have hlen : 4*x.outer.base.state.bits.length ≤ input.length := by
      simpa only [RecoveryCertificateRow.row_isSome,decide_eq_true_eq] using ha
    have hv := read_valid x word outerBits innerBits input hx hlen
    obtain ⟨hw,hk,hc⟩ := read_children_widths x.outer input hlen
    obtain ⟨last,hr1,hf1,hb1,hv1,ht1⟩ := row_run (readState x input) word outerBits innerBits prior innerRows rest innerRest
      hv hw hk hc hp hprior hi
    have hnext : RecoveryCalls.restarted rowMachine first.final.heads first.final.tapes=(readState x input).cfg rowMachine.start := by
      rw [hout0 ha]; rfl
    rw [←hnext] at hr1
    rw [ha] at ht0
    obtain ⟨r,hr,hb,hf⟩ := RecoveryGatedSequence.accept_run readMachine rowMachine 50
      (RecoveryRowFields.budget x.outer.base.state.bits.length) (rowCost (readState x input) outerBits)
      _ first last hr0 hh0 ht0 hr1
    have he : r.final=(readRowOutput x outerBits innerBits input).cfg r.final.control := by
      apply configuration_ext
      · rfl
      · rw [hf,hf1]; rfl
      · rw [hf,hf1]; rfl
    refine ⟨r,hr,hb,?_,?_,fun _=>⟨he,hv1,ht1⟩⟩
    · rw [he]; rfl
    · rw [he]
      change [(readRowOutput x outerBits innerBits input).outer.base.valid]=_
      simp only [readRowAnswer,ha,Bool.true_and]

end NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
