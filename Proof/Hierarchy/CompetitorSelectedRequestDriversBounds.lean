import Proof.Hierarchy.CompetitorSelectedRequestDrivers

namespace NearCubicWires.RepairOrdinary.CompetitorSelectedRequestDrivers
open MatrixScoreBatch CompetitorSelectedCount
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_bound (r : Request) (Q : ℕ) (hQ : Q≤r.p) :
    budget r Q≤5661*(r.U+1)^2*(r.d+r.p+1)^2 := by
  have hf := CompetitorSelectedRequestFields.budget_bound r
  have hd := CompetitorSelectedDimensions.budget_bound Q (extraWidth r) (r.U*r.U)
  have hw : Q+extraWidth r+1≤5*(r.d+r.p+1) := by
    have h := scalar_width_bound r Q hQ
    unfold scalarWidth at h
    omega
  have hu : r.U*r.U+1≤(r.U+1)^2 := by nlinarith
  have hs : r.d+r.p+1≤(r.d+r.p+1)^2 := Nat.le_self_pow (by decide) _
  have hd' : CompetitorSelectedDimensions.budget Q (extraWidth r) (r.U*r.U)≤
      640*(r.U+1)^2*(r.d+r.p+1)^2 := by
    apply hd.trans
    calc
      _ ≤ 128*(r.U+1)^2*(5*(r.d+r.p+1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 128 hu) hw
      _ = 640*(r.U+1)^2*(r.d+r.p+1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hs
  have hm : 1≤(r.U+1)^2*(r.d+r.p+1)^2 := by
    have h : 0 < (r.U+1)^2*(r.d+r.p+1)^2 := by positivity
    omega
  unfold budget
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorSelectedRequestDrivers
