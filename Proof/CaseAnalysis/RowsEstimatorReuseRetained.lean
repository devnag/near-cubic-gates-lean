import Proof.CaseAnalysis.RowsEstimatorReuseRun
import Proof.CaseAnalysis.RowsEstimatorNativeReadOnly

/-! The same enclosing reusable program preserves both externally owned
native tapes through the original estimator, masked reset, append and sweep. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
open LocalBitMultitape RepairRepresentation RecoveryRootRound
open RepairSource.RecoveryTseitinReadOnly
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem masked {t s : ℕ} (p : Machine t s) (mask : Fin t → Bool)
    (i : Fin t) (hp : NoWrite p i) : NoWrite (MaskedReset.machine p mask) (i.castAdd 1) := by
  intro state
  refine Fin.addCases (fun q bits a ha=>?_) (fun q bits a ha=>?_) state
  · by_cases hh : p.halted q=true
    · simp [MaskedReset.machine,hh] at ha
      subst a
      simp [Rewind.bridgeAction]
    · cases hr : p.rule q (fun j=>bits (j.castAdd 1)) with
      | none => simp [MaskedReset.machine,hh,hr] at ha
      | some b =>
        simp [MaskedReset.machine,hh,hr] at ha
        subst a
        simpa only [Rewind.recordAction,Fin.addCases_left] using hp q (fun j=>bits (j.castAdd 1)) b hr
  · simp only [MaskedReset.machine,Fin.addCases_right] at ha
    split at ha
    · split at ha
      · cases ha;simp [MaskedReset.rewindAction]
      · cases ha;simp [Rewind.finishAction]
    · contradiction

theorem after_readonly (p : Program) (i : Fin (tapes p))
    (hi : i=native p ∨ i=capacity p) : NoWrite (after p) i := by
  apply composition
  · apply unselected
    intro j he
    have hv:=congrArg (fun k : Fin (tapes p)=>k.val) he
    have ht : 70≤WholePrefix.tapes p:=by unfold WholePrefix.tapes;omega
    have hr:=record_private p
    rcases hi with rfl|rfl <;> fin_cases j
    all_goals simp [copySlots,native,capacity,old,output,log,Retained.capacity] at hv
    all_goals omega
  · exact unselected (eraseSlots p) _ i
      (erase_avoids p i (hi.elim Or.inl (fun h=>Or.inr (Or.inl h))))

private theorem protected_slot (p : Program) (i : Fin (WholePrefix.tapes p))
    (hi : i.val=52 ∨ i.val=68) : old p i=native p ∨ old p i=capacity p :=
  hi.elim (fun h=>Or.inl (Fin.ext h)) (fun h=>Or.inr (Fin.ext h))

theorem protected_readonly (a : WilliamsAlgorithm) (i : Fin (WholePrefix.tapes (producer a)))
    (hi : i.val=52 ∨ i.val=68) : NoWrite (machine a) (old (producer a) i) := by
  have original : NoWrite (Whole.machine a) i := by
    rcases hi with hi|hi
    · have he : i=NativeReadOnly.slot (producer a):=Fin.ext hi
      rw [he]
      exact NativeReadOnly.whole a
    · have he : i=Retained.capacity (producer a):=Fin.ext hi
      rw [he]
      exact Retained.whole_capacity a
  apply composition
  · exact embedded 2 (Reset.machine a) (i.castAdd 1)
      (masked (Whole.machine a) (Reset.selected (producer a)) i original)
  · exact after_readonly (producer a) (old (producer a) i)
      (protected_slot (producer a) i hi)

theorem native_run (a : WilliamsAlgorithm) (fuel : ℕ) (entry : Configuration _ _)
    (r : ExecutionReceipt _ _) (hr : runFrom (machine a) fuel entry=some r) :
    r.final.tapes (native (producer a))=entry.tapes (native (producer a)) :=
  run_tape (machine a) _
    (protected_readonly a (NativeReadOnly.slot (producer a)) (Or.inl rfl)) fuel entry r hr

theorem capacity_run (a : WilliamsAlgorithm) (fuel : ℕ) (entry : Configuration _ _)
    (r : ExecutionReceipt _ _) (hr : runFrom (machine a) fuel entry=some r) :
    r.final.tapes (capacity (producer a))=entry.tapes (capacity (producer a)) :=
  run_tape (machine a) _
    (protected_readonly a (Retained.capacity (producer a)) (Or.inr rfl)) fuel entry r hr

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
