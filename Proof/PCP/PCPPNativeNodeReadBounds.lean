import Proof.PCP.PCPPNativeNodeRead

namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeRead
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem field_budget (n : ℕ) : PCPPQueryNatural.budget n ≤ 64*(n+1)^2 := by
  have hw : natBitLength n ≤ n+1 := by
    unfold natBitLength
    exact Nat.add_le_add_right (Nat.log_le_self 2 n) 1
  unfold PCPPQueryNatural.budget MatrixDimensionPrepare.budget
  calc
    _ ≤ n*(8*(n+1)+10)+14*(n+1)+n+25 := by gcongr
    _ ≤ 64*(n+1)^2 := by nlinarith

theorem budget_bound (a b c : ℕ) : budget a b c ≤ 256*(a+b+c+1)^2 := by
  have ha := field_budget a
  have hb := field_budget b
  have hc := field_budget c
  have hpa : (a+1)^2 ≤ (a+b+c+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have hpb : (b+1)^2 ≤ (a+b+c+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have hpc : (c+1)^2 ≤ (a+b+c+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have hone : 1 ≤ (a+b+c+1)^2 := Nat.one_le_pow _ _ (by omega)
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.PCPPNativeNodeRead
