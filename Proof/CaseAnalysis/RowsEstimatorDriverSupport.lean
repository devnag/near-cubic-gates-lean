import Proof.CaseAnalysis.RowsEstimatorDriverRuntime

/-! The actual driver bank needs only a fixed number of D-cell sweeps. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverLayout
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def sweepCount (a : WilliamsAlgorithm) := 20*e a+2002

theorem value_positive (a : WilliamsAlgorithm) (d p G C : ℕ) : 1 ≤ Driver.value a d p G C := by
  unfold Driver.value
  omega

theorem input_bound (a : WilliamsAlgorithm) (d p G C : ℕ) (i : Fin (tapes a)) :
    (input a d p G C i).length ≤ Driver.value a d p G C := by
  have hm : d+p+G+1 ≤ (d+p+G+1)^3 := Nat.le_self_pow (by decide) _
  unfold input
  split_ifs <;> simp only [List.length_replicate,List.length_nil]
  all_goals unfold Driver.value
  all_goals omega

theorem fuel_support (a : WilliamsAlgorithm) (d p G C : ℕ) :
    budget a d p G C+1 ≤ sweepCount a*Driver.value a d p G C := by
  have hb := budget_linear a d p G C
  have hp := value_positive a d p G C
  have hmul := Nat.mul_le_mul_left (10*e a+1000) (show Driver.value a d p G C+1 ≤ 2*Driver.value a d p G C by omega)
  unfold sweepCount
  nlinarith only [hb,hp,hmul]

theorem support (a : WilliamsAlgorithm) (d p G C : ℕ) (out : Fin (tapes a) → List Bool)
    (hr : ClockJoin.ReadyRun (machine a) (budget a d p G C) (input a d p G C) out)
    (i : Fin (tapes a)) : (out i).length ≤ sweepCount a*Driver.value a d p G C := by
  obtain ⟨r,run,rt,_rh,rs⟩ := hr
  have hb := fuel_support a d p G C
  have hi := input_bound a d p G C i
  have hk : 1 ≤ sweepCount a := by unfold sweepCount;omega
  have hcap : Driver.value a d p G C ≤ sweepCount a*Driver.value a d p G C := by
    simpa only [one_mul] using Nat.mul_le_mul_right (Driver.value a d p G C) hk
  have h := CloseoutRowsProjectionReset.scratch_support (machine a) (budget a d p G C)
    (sweepCount a*Driver.value a d p G C) _ r run i rfl (hi.trans hcap) (by omega)
  rw [rt] at h
  exact h

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverLayout
