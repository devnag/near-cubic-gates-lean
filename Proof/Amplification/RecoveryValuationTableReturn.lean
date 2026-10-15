import Proof.Amplification.RecoveryRepeatRejectedTape

/-! Every return from the valuation loop retains the physical result head,
including malformed-row rejection. -/
namespace NearCubicWires.RepairOrdinary.RecoveryValuationTable
open LocalBitMultitape RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem row_supplier_tape (width : Nat) (x : Cursor) (hx : Inv width x) :
    ∃ r,runFrom RecoveryValuationStream.machine (budget width) (source x)=some r ∧
      r.steps≤budget width ∧ accepted r.final.control r.final.scanned=(next x).1 ∧
      ((next x).1=true  → r.final.heads=(source (next x).2).heads ∧
        r.final.tapes=(source (next x).2).tapes ∧ Inv width (next x).2) ∧
      ((next x).1=false  → r.final.heads 7=0 ∧ r.final.tapes 7=[false]) := by
  obtain ⟨hw,hi,hb,pre,hs,hp⟩ := hx
  obtain ⟨r,hr,ht,hh,hf,hcost⟩ := bounded_read x.data pre x.rest hs hp
    (hi.trans hw.symm) (by simpa only [hw] using hb)
  refine ⟨r,by simpa only [source,hw] using hr,by simpa only [hw] using hcost,?_,?_,?_⟩
  · simp only [accepted,Configuration.scanned,hh,ht,next]
    rfl
  · intro ha
    have he := hf ha
    refine ⟨?_,?_,next_inv width x ⟨hw,hi,hb,pre,hs,hp⟩ ha⟩
    · rw [he]; rfl
    · rw [he]; rfl
  · intro ha
    change (readEntry x.data.width x.rest).isSome=false at ha
    exact ⟨hh,by simpa only [ha] using ht⟩

theorem table_return (width total : Nat) (x : Cursor) (hx : Inv width x) :
    ∃ r,runFrom machine (total*(budget width+3)+3)
        (RepeatMachine.cfg 0 (source x) total 1)=some r ∧
      r.steps≤total*(budget width+3)+3 ∧
      RepeatMachine.Result source total (RepeatMachine.iterate next total x) r.final ∧
      r.final.heads 7=0 ∧
      ((readMany (readEntry x.data.width) total x.rest).isSome=false  → r.final.tapes 7=[false]) := by
  obtain ⟨r,hr,ht,hf,hbad⟩ := RepeatMachine.rejecting_repeat_tape RecoveryValuationStream.machine
    accepted source next (Inv width) (budget width) 7 (by intro x _; rfl) (row_supplier_tape width) total x hx
  have hh : r.final.heads 7=0 := by
    cases ha : (RepeatMachine.iterate next total x).1 with
    | false => exact (hbad ha).1
    | true =>
      simp only [RepeatMachine.Result,ha,↓reduceIte] at hf
      rw [hf]
      rfl
  refine ⟨r,hr,ht,hf,hh,?_⟩
  intro ha
  rw [←iterate_accepts] at ha
  exact (hbad ha).2

end NearCubicWires.RepairOrdinary.RecoveryValuationTable
