import Proof.Hierarchy.CompetitorCountRecordRequest
import Proof.Hierarchy.CompetitorSelectedRequestDriversBounds

namespace NearCubicWires.RepairOrdinary.CompetitorCountRecordRequest
open MatrixScoreBatch CompetitorSelectedCount
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_bound (r : Request) (Q : ℕ) (hQ : Q≤r.p) :
    budget r Q≤1034000*(r.U+1)^2*(r.d+r.p+1)^2 := by
  have hd := CompetitorSelectedRequestDrivers.budget_bound r Q hQ
  have hc := CompetitorSelectedCount.budget_bound Q (scalarWidth r Q) (r.U*r.U)
  have ha := CompetitorCountRecordAppend.budget_bound (scalarWidth r Q)
  have hw := scalar_width_bound r Q hQ
  have hsum : Q+scalarWidth r Q+1≤5*(r.d+r.p+1) := by omega
  have hwide : scalarWidth r Q+1≤5*(r.d+r.p+1) := by omega
  have hgrid : r.U*r.U+1≤(r.U+1)^2 := by nlinarith
  have hscale : r.d+r.p+1≤(r.d+r.p+1)^2 := Nat.le_self_pow (by decide) _
  have hcount : CompetitorSelectedCount.budget Q (scalarWidth r Q) (r.U*r.U)≤
      320*(r.U+1)^2*(r.d+r.p+1)^2 := by
    apply hc.trans
    calc
      _ ≤ 64*(r.U+1)^2*(5*(r.d+r.p+1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 64 hgrid) hsum
      _ = 320*(r.U+1)^2*(r.d+r.p+1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hscale
  have hAppend : CompetitorCountRecordAppend.budget (scalarWidth r Q)≤
      1027500*(r.U+1)^2*(r.d+r.p+1)^2 := by
    apply ha.trans
    have hp := Nat.pow_le_pow_left hwide 2
    have hu : 1≤(r.U+1)^2 := by
      have h : 0<(r.U+1)^2 := by positivity
      omega
    calc
      _ ≤ 41100*(5*(r.d+r.p+1))^2 := Nat.mul_le_mul_left _ hp
      _ = 1027500*(r.d+r.p+1)^2 := by ring
      _ ≤ _ := by nlinarith
  have hm : 1≤(r.U+1)^2*(r.d+r.p+1)^2 := by
    have h : 0<(r.U+1)^2*(r.d+r.p+1)^2 := by positivity
    omega
  unfold budget CompetitorSelectedRequestCount.budget CompetitorSelectedCount.coldBudget
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorCountRecordRequest
