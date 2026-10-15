import Proof.Circuits.PolynomialClockPower

/-! A uniform explicit coefficient pays short binary powering within the
quadratic-or-higher hierarchy clock, while preserving its sharper ledger. -/
namespace NearCubicWires.RepairOrdinary.PolynomialClockPower
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem square_le_dyadic (m : ℕ) : (m+1)^2 ≤ 4*2^m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rcases m with _ | m
    · norm_num
    rcases m with _ | m
    · norm_num
    simp only [pow_succ] at ih ⊢
    nlinarith

theorem dyadic_ell_bound (n : ℕ) : 2^PCPResourceLedger.ell n ≤ 2*(n+1) := by
  by_cases hz : PCPResourceLedger.ell n=0
  · rw [hz]; simp; omega
  · have hp : PCPResourceLedger.ell n-1<PCPResourceLedger.ell n := by omega
    have h := Nat.pow_lt_of_lt_clog (b:=2) (x:=n+1) hp
    have he : PCPResourceLedger.ell n=(PCPResourceLedger.ell n-1)+1 := by omega
    rw [he,pow_succ]
    omega

theorem q_square_bound (n : ℕ) : (PCPResourceLedger.ell n+1)^2 ≤ 8*(n+1) := by
  have h := square_le_dyadic (PCPResourceLedger.ell n)
  have hd := dyadic_ell_bound n
  omega

theorem square_le_power (k n : ℕ) : (n+1)^2 ≤ 4*(n^(k+2)+1) := by
  by_cases hn : n=0
  · subst n; simp
  · have hp : 1 ≤ n^k := Nat.one_le_pow _ _ (by omega)
    have hs : n^2 ≤ n^(k+2) := by rw [pow_add]; nlinarith
    nlinarith

def finalCoefficient (D : ℕ) := coefficient D+8*HierarchyReduction.shortCoefficient D 1+12

theorem final_budget_bound (D : ℕ) (bits : List Bool) :
    budget D bits+8*HierarchyBinary.width 1 D bits.length+12 ≤
      finalCoefficient D*(bits.length+1)*(PCPResourceLedger.ell bits.length+1)^2 := by
  have hp := budget_bound D bits
  let X := (bits.length+1)*(PCPResourceLedger.ell bits.length+1)^2
  have hX : 1 ≤ X := by
    have hx : 0<X := by dsimp [X]; positivity
    omega
  have hL : PCPResourceLedger.ell bits.length+1 ≤ X := by
    have h : PCPResourceLedger.ell bits.length+1 ≤ (PCPResourceLedger.ell bits.length+1)^2 :=
      Nat.le_self_pow (by decide) _
    dsimp [X]; nlinarith
  have hw : HierarchyBinary.width 1 D bits.length ≤
      HierarchyReduction.shortCoefficient D 1*(PCPResourceLedger.ell bits.length+1) := by
    dsimp [HierarchyBinary.width,HierarchyReduction.shortCoefficient]
    nlinarith
  have hw' := hw.trans (Nat.mul_le_mul_left (HierarchyReduction.shortCoefficient D 1) hL)
  rw [Nat.mul_assoc] at hp
  change budget D bits ≤ coefficient D*X at hp
  rw [Nat.mul_assoc]
  change _ ≤ finalCoefficient D*X
  unfold finalCoefficient
  nlinarith

theorem ordinary_budget_bound (k n : ℕ) :
    finalCoefficient (k+2)*(n+1)*(PCPResourceLedger.ell n+1)^2 ≤
      (32*finalCoefficient (k+2))*(n^(k+2)+1) := by
  calc
    _ ≤ finalCoefficient (k+2)*(n+1)*(8*(n+1)) :=
      Nat.mul_le_mul_left _ (q_square_bound n)
    _ = (8*finalCoefficient (k+2))*(n+1)^2 := by ring
    _ ≤ (8*finalCoefficient (k+2))*(4*(n^(k+2)+1)) :=
      Nat.mul_le_mul_left _ (square_le_power k n)
    _ = _ := by ring

end NearCubicWires.RepairOrdinary.PolynomialClockPower
