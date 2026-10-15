import Proof.CaseAnalysis.RowsEstimatorActual

/-! Native cut bytes and their original C driver remain read-only through
the warm estimator, its ordinary rewind, scalar append and private sweep. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmActual
open LocalBitMultitape RepairRepresentation RecoveryRootRound
open RepairSource.RecoveryTseitinReadOnly
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem warm_readonly (a : WilliamsAlgorithm) (i : Fin (WholePrefix.tapes (producer a)))
    (hi : i.val=52 ∨ i.val=68) : NoWrite (Warm.machine a) i := by
  apply composition
  · rcases hi with hi|hi
    · have he : i=Warm.headerSlots (producer a) 52 := Fin.ext hi
      rw [he]
      exact focus _ (Warm.header_injective (producer a)) _ 52
        (CloseoutCaseTwo.AddressRetention.frame_readonly Header.machine 51 52 (by decide) NativeReadOnly.header)
    · apply unselected
      intro j he
      have hv := congrArg (fun k : Fin (WholePrefix.tapes (producer a)) => k.val) he
      have hj := (Framed.slots j).isLt
      simp only [Warm.headerSlots,Fin.val_castAdd,hi] at hv
      omega
  · apply unselected
    intro j he
    have hv := congrArg (fun k : Fin (WholePrefix.tapes (producer a)) => k.val) he
    simp only [WholePrefix.slots] at hv
    rcases hi with hi|hi
    all_goals split_ifs at hv <;> simp only [Fin.val_natAdd,hi] at hv <;> omega

theorem reuse_readonly {s : ℕ} (p : Program) (worker : Machine (WholePrefix.tapes p) s)
    (i : Fin (WholePrefix.tapes p)) (hi : i.val=52 ∨ i.val=68) (hp : NoWrite worker i) :
    NoWrite (WarmReuse.machine p worker) (Reuse.old p i) := by
  apply composition
  · exact embedded 2 (Rewind.machine worker) (i.castAdd 1) (rewind worker i hp)
  · exact Reuse.after_readonly p (Reuse.old p i)
      (hi.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h)))

theorem protected_readonly (a : WilliamsAlgorithm) (i : Fin (WholePrefix.tapes (producer a)))
    (hi : i.val=52 ∨ i.val=68) : NoWrite (machine a) (Reuse.old (producer a) i) :=
  reuse_readonly (producer a) (Warm.machine a) i hi (warm_readonly a i hi)

theorem native_run (a : WilliamsAlgorithm) (fuel : ℕ) (start : Configuration _ _)
    (r : ExecutionReceipt _ _) (hr : runFrom (machine a) fuel start=some r) :
    r.final.tapes (Reuse.native (producer a))=start.tapes (Reuse.native (producer a)) :=
  run_tape (machine a) _
    (protected_readonly a (NativeReadOnly.slot (producer a)) (Or.inl rfl)) fuel start r hr

theorem capacity_run (a : WilliamsAlgorithm) (fuel : ℕ) (start : Configuration _ _)
    (r : ExecutionReceipt _ _) (hr : runFrom (machine a) fuel start=some r) :
    r.final.tapes (Reuse.capacity (producer a))=start.tapes (Reuse.capacity (producer a)) :=
  run_tape (machine a) _
    (protected_readonly a (Retained.capacity (producer a)) (Or.inr rfl)) fuel start r hr

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmActual
