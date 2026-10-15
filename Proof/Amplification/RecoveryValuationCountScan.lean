import Proof.Amplification.RecoveryValuationCountGraph

/-! The whole capped valuation-list scan executes count production, every
row comparison, all call returns, and the final physical acceptance write.
The bound depends only on the query-derived width and cap. -/
namespace NearCubicWires.RepairOrdinary.RecoveryValuationCount
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bounded_list (d : Data) (pre word : List Bool) (cap : Nat)
    (hs : d.source=pre++frame word) (hp : d.pos=pre.length)
    (hi : d.index.length=d.width) (hb : d.row.length≤2*(d.width+1)+1) :
    ∃ r,runFrom machine (limit d.width cap) (cfg d 0 cap machine.start)=some r ∧
      r.steps≤limit d.width cap ∧ r.final.heads 7=0 ∧
      r.final.tapes 7=[(readList cap (readEntry d.width) word).isSome] ∧
      ∀ count rest,readCount cap word=some (count,rest) →
        (readMany (readEntry d.width) count rest).isSome=true →
        r.final=finished (cfg (RepeatMachine.iterate RecoveryValuationTable.next count
          (⟨counted d count,rest⟩ : RecoveryValuationTable.Cursor)).2.data count cap
            (RepeatMachine.phaseCode (Fintype.card (RecoveryCalls.Control RecoveryValuationStream.sizes)) 3)) true := by
  obtain ⟨r0,hr0,_,hc0,hf0⟩ := count_run d pre word cap hs hp
  cases hcount : readCount cap word with
  | none =>
    have hc : r0.final.control≠3 := by
      intro he
      have hh := hc0.mp he
      rw [hcount] at hh
      contradiction
    obtain ⟨hh0,ht0⟩ := count_preserves_flag d pre word cap hs hp r0 hr0
    obtain ⟨n0,hn0,h0⟩ := call_receipt graphSizes programs 0 next 0 3 _ _ r0 hr0 (by
      simp only [next]
      have hv : r0.final.control.val≠3 := by intro he; exact hc (Fin.ext he)
      simp [hv])
    change Timed machine n0 (cfg d 0 cap machine.start) (flagStart r0.final false) at h0
    obtain ⟨n1,hn1,h1⟩ := flag_tail r0.final d.valid false hh0 ht0
    have h := h0.trans h1
    have hn : n0+n1≤limit d.width cap := by unfold limit; nlinarith
    obtain ⟨r,hr,hf,ht⟩ := h.run (by simp [finished,RecoveryCalls.machine,RecoveryCalls.stopped])
    have hm := runFrom_moreFuel machine (n0+n1) (limit d.width cap-(n0+n1)) _ r hr
    rw [Nat.add_sub_of_le hn] at hm
    refine ⟨r,hm,ht.le.trans hn,?_,?_,?_⟩
    · simpa only [hf,finished,RecoveryCalls.stopped] using hh0
    · simp [hf,finished,RecoveryCalls.stopped,readList_count_none d.width cap word hcount]
    · intro count rest he
      contradiction
  | some pair =>
    rcases pair with ⟨count,rest⟩
    obtain ⟨hcap,hout0⟩ := hf0 count rest hcount
    obtain ⟨n0,hn0,h0⟩ := call_receipt graphSizes programs 0 next 0 1 _ _ r0 hr0 (by rw [hout0]; rfl)
    rw [hout0] at h0
    change Timed machine n0 (cfg d 0 cap machine.start)
      (cfg (counted d count) count cap (RecoveryCalls.code graphSizes 1 loopMachine.start)) at h0
    let x : RecoveryValuationTable.Cursor := ⟨counted d count,rest⟩
    have hx : RecoveryValuationTable.Inv d.width x := count_cursor d d.width cap count pre word rest hi rfl hb hs hp hcount
    obtain ⟨r1,hr1,_,hh1,⟨old,ht1⟩,hc1,hout1⟩ := loop_run d.width count cap x hx
    let bit : Bool := (readMany (readEntry d.width) count rest).isSome
    have hbit : decide (r1.final.control.val=(RepeatMachine.phaseCode (Fintype.card (RecoveryCalls.Control RecoveryValuationStream.sizes)) 3).val)=bit := by
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq]
      exact Fin.val_inj.trans hc1
    obtain ⟨n1,hn1,h1⟩ := call_receipt graphSizes programs 0 next 1 (stage bit) _ _ r1 hr1 (by
      change some (stage (decide (r1.final.control.val=(RepeatMachine.phaseCode (Fintype.card (RecoveryCalls.Control RecoveryValuationStream.sizes)) 3).val)))=some (stage bit)
      rw [hbit])
    change Timed machine n1
      (cfg (counted d count) count cap (RecoveryCalls.code graphSizes 1 loopMachine.start)) (flagStart r1.final bit) at h1
    obtain ⟨n2,hn2,h2⟩ := flag_tail r1.final old bit hh1 ht1
    have h := (h0.trans h1).trans h2
    have hn : n0+n1+n2≤limit d.width cap := by
      have hm := Nat.mul_le_mul_right (budget d.width+3) hcap
      unfold limit
      nlinarith
    obtain ⟨r,hr,hf,ht⟩ := h.run (by simp [finished,RecoveryCalls.machine,RecoveryCalls.stopped])
    have hm := runFrom_moreFuel machine (n0+n1+n2) (limit d.width cap-(n0+n1+n2)) _ r hr
    rw [Nat.add_sub_of_le hn] at hm
    refine ⟨r,hm,ht.le.trans hn,?_,?_,?_⟩
    · simpa only [hf,finished,RecoveryCalls.stopped] using hh1
    · simp [hf,finished,RecoveryCalls.stopped,readList_count_some d.width cap count word rest hcount,bit]
    · intro count' rest' he ha
      have hpairs : (count,rest)=(count',rest') := Option.some.inj he
      cases hpairs
      have htrue : bit=true := ha
      rw [hf,htrue,hout1 ha]

end NearCubicWires.RepairOrdinary.RecoveryValuationCount
