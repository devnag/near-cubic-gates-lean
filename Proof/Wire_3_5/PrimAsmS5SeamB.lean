import Proof.Wire_3_5.PrimAsmS5Seam

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (E3 : SymPtEval)

/-- The ledger's load `ψ = psiOf n` at the request's width. -/
noncomputable abbrev s5Psi (r : FReq l F kclk coef A a ha) : ℕ := ((gate0 l F).budget kclk coef A a ha).psiOf r.1.n

/-- **The preprocessing-class cost bound** `C · 2^{D·ψ} · (|fpIn| + 1)^D`. -/
noncomputable def s5Bound (C D : ℕ) (r : FReq l F kclk coef A a ha) : ℕ :=
  C * 2 ^ (D * s5Psi l F kclk coef A a ha r) * ((fpIn l F kclk coef A a ha r).length + 1) ^ D

theorem s5Bound_mono (C C' D D' : ℕ) (hC : C ≤ C') (hD : D ≤ D') (r : FReq l F kclk coef A a ha) :
    s5Bound l F kclk coef A a ha C D r ≤ s5Bound l F kclk coef A a ha C' D' r := by
  unfold s5Bound
  have h1 : 2 ^ (D * s5Psi l F kclk coef A a ha r) ≤ 2 ^ (D' * s5Psi l F kclk coef A a ha r) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hD)
  have h2 : ((fpIn l F kclk coef A a ha r).length + 1) ^ D ≤ ((fpIn l F kclk coef A a ha r).length + 1) ^ D' :=
    Nat.pow_le_pow_right (by omega) hD
  exact Nat.mul_le_mul (Nat.mul_le_mul hC h1) h2

theorem one_le_s5Bound (C D : ℕ) (hC : 1 ≤ C) (r : FReq l F kclk coef A a ha) :
    1 ≤ s5Bound l F kclk coef A a ha C D r := by
  unfold s5Bound
  have h1 : 1 ≤ 2 ^ (D * s5Psi l F kclk coef A a ha r) := Nat.one_le_two_pow
  have h2 : 1 ≤ ((fpIn l F kclk coef A a ha r).length + 1) ^ D := Nat.one_le_pow _ _ (by omega)
  calc 1 = 1 * 1 * 1 := by ring
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul hC h1) h2

/-- **The THR half with its cost bound** (the target). -/
structure S5ThrB (L : S5Lay E3.nw) extends S5Thr l F kclk coef A a ha E3 L where
  Ct : ℕ
  Dt : ℕ
  cost_le : ∀ r, cost r ≤ s5Bound l F kclk coef A a ha Ct Dt r

/-- **The core half with its cost bound** (the target). -/
structure S5CoreB (L : S5Lay E3.nw) extends S5Core l F kclk coef A a ha E3 L where
  Cc : ℕ
  Dcc : ℕ
  cost_le : ∀ r, cost r ≤ s5Bound l F kclk coef A a ha Cc Dcc r

/-- **The halves in sequence** (one bridge step): within `s5Bound (Ct + Cc + 1) (max Dt Dcc)`. -/
theorem s5_cost_le (L : S5Lay E3.nw) (T : S5ThrB l F kclk coef A a ha E3 L) (K : S5CoreB l F kclk coef A a ha E3 L)
    (r : FReq l F kclk coef A a ha) :
    T.cost r + 1 + K.cost r ≤ s5Bound l F kclk coef A a ha (T.Ct + K.Cc + 1) (max T.Dt K.Dcc) r := by
  have h1 := le_trans (T.cost_le r) (s5Bound_mono l F kclk coef A a ha T.Ct T.Ct T.Dt (max T.Dt K.Dcc) le_rfl
    (le_max_left _ _) r)
  have h2 := le_trans (K.cost_le r) (s5Bound_mono l F kclk coef A a ha K.Cc K.Cc K.Dcc (max T.Dt K.Dcc) le_rfl
    (le_max_right _ _) r)
  have h3 := one_le_s5Bound l F kclk coef A a ha 1 (max T.Dt K.Dcc) le_rfl r
  have hadd : ∀ C C' : ℕ, s5Bound l F kclk coef A a ha (C + C') (max T.Dt K.Dcc) r =
      s5Bound l F kclk coef A a ha C (max T.Dt K.Dcc) r + s5Bound l F kclk coef A a ha C' (max T.Dt K.Dcc) r := by
    intro C C'; unfold s5Bound; ring
  rw [hadd, hadd]
  omega

end Family

end NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
