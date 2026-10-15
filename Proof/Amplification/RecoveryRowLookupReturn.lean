import Proof.Amplification.RecoveryRowLookupResult

/-! Physical success bit for the whole prior-row scan. A failed body keeps its
actual false cell; successful scans, including the empty prefix, retain true.
This is the bit consumed after the paid local rewind. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowLookupTable
open LocalBitMultitape RecoveryRowLookupStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem row_supplier_tape (width : Nat) (x : Cursor) (hx : Inv width x) :
    ∃ r,runFrom RecoveryRowLookupStream.machine (budget width) (source x)=some r ∧
      r.steps≤budget width ∧ accepted r.final.control r.final.scanned=(next x).1 ∧
      ((next x).1=true → r.final.heads=(source (next x).2).heads ∧
        r.final.tapes=(source (next x).2).tapes ∧ Inv width (next x).2) ∧
      ((next x).1=false → r.final.heads 6=0 ∧ r.final.tapes 6=[false]) := by
  rcases hx with ⟨hd,hw,pre,hs,hp⟩
  obtain ⟨r,hr,ht,hh,hflag,hgood⟩ := row_run x.data pre x.rest hd hs hp
  refine ⟨r,by simpa only [source,hw] using hr,by simpa only [hw] using ht,?_,?_,?_⟩
  · simp only [accepted,Configuration.scanned,hh,hflag,next]
    rfl
  · intro ha
    obtain ⟨he,_⟩ := hgood ha
    refine ⟨?_,?_,next_inv width x ⟨hd,hw,pre,hs,hp⟩ ha⟩
    · rw [he]; rfl
    · rw [he]; rfl
  · intro ha
    change (readRow x.data.row.width x.rest).isSome=false at ha
    exact ⟨hh,by rw [hflag,ha]⟩

theorem iterate_valid_bit (total : Nat) (x : Cursor) (hv : x.data.row.valid=true)
    (ha : (RepeatMachine.iterate next total x).1=true) :
    (RepeatMachine.iterate next total x).2.data.row.valid=true := by
  induction total generalizing x with
  | zero => exact hv
  | succ total ih =>
    cases hh : (next x).1 with
    | false => simp [RepeatMachine.iterate,hh] at ha
    | true =>
      simp only [RepeatMachine.iterate,hh,↓reduceIte] at ha ⊢
      exact ih (next x).2 rfl ha

theorem table_return (width total : Nat) (x : Cursor) (hx : Inv width x)
    (hv : x.data.row.valid=true) :
    ∃ r,runFrom machine (total*(budget width+3)+3)
        (RepeatMachine.cfg 0 (source x) total 1)=some r ∧
      r.steps≤total*(budget width+3)+3 ∧
      RepeatMachine.Result source total (RepeatMachine.iterate next total x) r.final ∧
      r.final.heads 6=0 ∧
      r.final.tapes 6=[(readMany (readRow x.data.row.width) total x.rest).isSome] := by
  obtain ⟨r,hr,ht,hf,hbad⟩ := RepeatMachine.rejecting_repeat_tape RecoveryRowLookupStream.machine
    accepted source next (Inv width) (budget width) 6 (by intro x _; rfl) (row_supplier_tape width) total x hx
  refine ⟨r,hr,ht,hf,?_,?_⟩
  · cases ha : (RepeatMachine.iterate next total x).1 with
    | false => exact (hbad ha).1
    | true =>
      simp only [RepeatMachine.Result,ha,↓reduceIte] at hf
      rw [hf]
      rfl
  · rw [←iterate_accepts]
    cases ha : (RepeatMachine.iterate next total x).1 with
    | false => exact (hbad ha).2
    | true =>
      have hv' := iterate_valid_bit total x hv ha
      simp only [RepeatMachine.Result,ha,↓reduceIte] at hf
      rw [hf]
      change [(RepeatMachine.iterate next total x).2.data.row.valid]=[true]
      rw [hv']

end NearCubicWires.RepairOrdinary.RecoveryRowLookupTable
