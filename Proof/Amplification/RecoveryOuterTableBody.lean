import Proof.Amplification.RecoveryOuterTableAdvance

namespace NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def bodyMachine := RecoveryGatedSequence.machine readRowMachine advanceMachine 50

theorem body_run (x : State) (word outerBits innerBits pre input : List Bool)
    (prior innerRows : List Row) (rest innerRest : List Bool) (limit : Nat)
    (hx : x.Valid word outerBits innerBits)
    (hs : x.outer.base.source=pre++frame input) (hpos : x.outer.base.pos=pre.length)
    (hp : readMany (readRow x.outer.bank.row.width) x.outer.total outerBits=some (prior,rest))
    (hprior : checkFrom [] prior=true)
    (hi : readMany (readRow x.inner.row.width) x.total innerBits=some (innerRows,innerRest))
    (hj : x.outer.total ≤ limit) (hn : x.total ≤ limit)
    (hcap : (x.outer.total+1)*(RecoveryRowLookupStream.budget x.outer.bank.row.width+3)+5 ≤ x.outer.lookupCapacity) :
    ∃ r,runFrom bodyMachine (tableBudget x.outer.base.state.bits.length limit) (x.cfg bodyMachine.start)=some r ∧
      r.steps ≤ tableBudget x.outer.base.state.bits.length limit ∧ r.final.heads 50=0 ∧
      r.final.tapes 50=[readRowAnswer x outerBits innerBits input] ∧
      (readRowAnswer x outerBits innerBits input=true →
        r.final=(rowAdvanced x outerBits innerBits input).cfg r.final.control ∧
        (rowAdvanced x outerBits innerBits input).Valid word outerBits innerBits) := by
  have hbudget := read_row_time_le x outerBits input x.outer.base.state.bits.length limit rfl
    hx.1.2.1.2.1.le hj hx.2.2.1.2.1.le hn
  obtain ⟨first,hr0,hb0,hh0,ht0,hout0⟩ := read_row_run x word outerBits innerBits pre input prior innerRows rest innerRest
    hx hs hpos hp hprior hi
  cases ha : readRowAnswer x outerBits innerBits input
  · rw [ha] at ht0
    obtain ⟨r,hr,hb,hf⟩ := RecoveryGatedSequence.reject_run readRowMachine advanceMachine 50
      (readRowCost x outerBits input) _ first hr0 hh0 ht0
    have hl : readRowCost x outerBits input+1 ≤ tableBudget x.outer.base.state.bits.length limit := by omega
    have hm := runFrom_moreFuel bodyMachine _ (tableBudget x.outer.base.state.bits.length limit-
      (readRowCost x outerBits input+1)) _ r hr
    rw [Nat.add_sub_of_le hl] at hm
    refine ⟨r,hm,hb.trans hl,?_,?_,?_⟩
    · rw [hf]; exact hh0
    · rw [hf]; change first.final.tapes 50=_; exact ht0
    · simp only [Bool.false_eq_true,IsEmpty.forall_iff]
  · have hread : (readRow x.outer.base.state.bits.length input).isSome=true := by
      have h:=ha
      simp only [readRowAnswer,Bool.and_eq_true] at h
      exact h.1
    have hlen : 4*x.outer.base.state.bits.length ≤ input.length := by
      simpa only [RecoveryCertificateRow.row_isSome,decide_eq_true_eq] using hread
    obtain ⟨hf0,hvalid,_⟩ := hout0 hread
    have htotal := (read_output_retained x outerBits innerBits input hlen).2.2.1
    obtain ⟨last,hr1,hf1,hb1⟩ := advance_run (readRowOutput x outerBits innerBits input)
    rw [htotal] at hr1 hb1
    have hnext : RecoveryCalls.restarted advanceMachine first.final.heads first.final.tapes=
        (readRowOutput x outerBits innerBits input).cfg advanceMachine.start := by
      rw [hf0]; rfl
    rw [←hnext] at hr1
    rw [ha] at ht0
    obtain ⟨r,hr,hb,hf⟩ := RecoveryGatedSequence.accept_run readRowMachine advanceMachine 50
      (readRowCost x outerBits input) (2*x.outer.total+6) _ first last hr0 hh0 ht0 hr1
    have hl : readRowCost x outerBits input+(2*x.outer.total+6)+2 ≤ tableBudget x.outer.base.state.bits.length limit := by omega
    have hm := runFrom_moreFuel bodyMachine _ (tableBudget x.outer.base.state.bits.length limit-
      (readRowCost x outerBits input+(2*x.outer.total+6)+2)) _ r hr
    rw [Nat.add_sub_of_le hl] at hm
    have he : r.final=(rowAdvanced x outerBits innerBits input).cfg r.final.control := by
      apply configuration_ext
      · rfl
      · rw [hf,hf1]; rfl
      · rw [hf,hf1]; rfl
    refine ⟨r,hm,hb.trans hl,?_,?_,fun _=>⟨he,row_advanced_valid x word outerBits innerBits input hx hvalid hlen hcap⟩⟩
    · rw [he]; rfl
    · rw [he]
      change [(readRowOutput x outerBits innerBits input).outer.base.valid]=_
      have hvalidBit : (readRowOutput x outerBits innerBits input).outer.base.valid=true := by
        simpa only [readRowAnswer,hread,Bool.true_and] using ha
      rw [hvalidBit]

end NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
