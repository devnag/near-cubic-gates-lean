import Proof.CaseAnalysis.RowsEstimatorDriverIterate

/-! Fixed D-driven cleanup passes, with actual receipts at every boundary. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverPasses
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def forward (t K : ℕ) := DriverIterate.machine (DriverSweep.round t) K
noncomputable def back (t K : ℕ) := DriverIterate.machine (DriverReturnMany.machine t) K

theorem forward_run {t : ℕ} (D K : ℕ) (data : Fin t → List Bool) : ∃ r,
    runFrom (forward t K) (K*(3*D+5))
      (DriverIterate.cfg (DriverSweep.round t) K (DriverSweep.heads t 0) (DriverSweep.words D 0 data))=some r ∧
      r.final.heads=DriverSweep.heads t (K*D) ∧
      r.final.tapes=DriverSweep.words D (K*D) data ∧ r.steps=K*(3*D+5) := by
  have step : ∀ n,∃ r,runFrom (DriverSweep.round t) (3*D+4)
      ⟨(DriverSweep.round t).start,DriverSweep.heads t (n*D),DriverSweep.words D (n*D) data⟩=some r ∧
      r.final.heads=DriverSweep.heads t ((n+1)*D) ∧
      r.final.tapes=DriverSweep.words D ((n+1)*D) data ∧ r.steps=3*D+4 := by
    intro n
    obtain ⟨r,hr,rh,rt,rs⟩ := DriverSweep.round_run D (n*D) data
    refine ⟨r,hr,?_,?_,rs⟩
    · simpa only [Nat.add_mul,Nat.one_mul] using rh
    · simpa only [Nat.add_mul,Nat.one_mul] using rt
  simpa only [forward,Nat.zero_mul,Nat.add_assoc] using
    DriverIterate.run (DriverSweep.round t) (3*D+4)
      (fun n => DriverSweep.heads t (n*D)) (fun n => DriverSweep.words D (n*D) data) step K

theorem back_run {t : ℕ} (D K pos : ℕ) (data : Fin t → List Bool) : ∃ r,
    runFrom (back t K) (K*(2*D+5))
      (DriverIterate.cfg (DriverReturnMany.machine t) K
        (DriverReturnMany.cfg 0 D pos data).heads (DriverReturnMany.cfg 0 D pos data).tapes)=some r ∧
      r.final.heads=(DriverReturnMany.cfg 0 D (pos-K*(D+1)) data).heads ∧
      r.final.tapes=(DriverReturnMany.cfg 0 D pos data).tapes ∧ r.steps=K*(2*D+5) := by
  have step : ∀ n,∃ r,runFrom (DriverReturnMany.machine t) (2*D+4)
      ⟨(DriverReturnMany.machine t).start,(DriverReturnMany.cfg 0 D (pos-n*(D+1)) data).heads,
        (DriverReturnMany.cfg 0 D pos data).tapes⟩=some r ∧
      r.final.heads=(DriverReturnMany.cfg 0 D (pos-(n+1)*(D+1)) data).heads ∧
      r.final.tapes=(DriverReturnMany.cfg 0 D pos data).tapes ∧ r.steps=2*D+4 := by
    intro n
    obtain ⟨r,hr,rf,rs⟩ := DriverReturnMany.run D (pos-n*(D+1)) data
    refine ⟨r,hr,?_,?_,rs⟩
    · rw [rf]
      simp only [Nat.add_mul,Nat.one_mul,Nat.sub_sub]
      rfl
    · rw [rf]
      rfl
  simpa only [back,Nat.zero_mul,Nat.sub_zero,Nat.add_assoc] using
    DriverIterate.run (DriverReturnMany.machine t) (2*D+4)
      (fun n => (DriverReturnMany.cfg 0 D (pos-n*(D+1)) data).heads)
      (fun _ => (DriverReturnMany.cfg 0 D pos data).tapes) step K

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverPasses
