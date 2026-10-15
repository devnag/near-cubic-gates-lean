import Proof.CaseAnalysis.RowsTouchingGateFoldLayout
import Proof.Hierarchy.HierarchySourceScales

/-! The exact paper ceiling logarithm comes from the bit length of q+1.
This identity includes the powers-of-two boundary and q=0. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.LiveCount
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem logarithm (q : ℕ):logScale q=natBitLength (q+1):=by
  apply Nat.le_antisymm
  · change Nat.clog 2 (q+2)≤Nat.log 2 (q+1)+1
    apply Nat.clog_le_of_le_pow
    have fit:=Nat.lt_pow_succ_log_self (by decide : 1<2) (q+1)
    omega
  · change Nat.log 2 (q+1)+1≤Nat.clog 2 (q+2)
    rw [Nat.add_one_le_iff,Nat.lt_clog_iff_pow_lt (by decide : 1<2)]
    have below:=Nat.pow_log_le_self 2 (by omega : q+1≠0)
    omega

theorem logarithm_le (q : ℕ):logScale q≤q+1:=by
  apply Nat.clog_le_of_le_pow
  have fit:q+1<2^(q+1):=Nat.lt_two_pow_self
  omega

theorem live_count (q kappa : ℕ):SupplierEstimator.normalizedLiveCount q kappa=
    min q (kappa*natBitLength (q+1)):=by
  rw [SupplierEstimator.normalizedLiveCount,logarithm]

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.LiveCount
