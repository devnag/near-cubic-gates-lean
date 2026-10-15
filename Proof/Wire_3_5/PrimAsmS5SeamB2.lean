import Proof.Wire_3_5.PrimAsmS5Seam2

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.BlockPlatform NearCubicWires.ExtDecompositionBatch

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (Sw : SymWords)

/-- **The THR half with its cost bound** (the target): `s5Bound`'s preprocessing form. -/
structure S5ThrB2 (L : S5Lay Sw.nw) extends S5Thr2 l F kclk coef A a ha Sw L where
  Ct : ℕ
  Dt : ℕ
  cost_le : ∀ r, cost r ≤ s5Bound l F kclk coef A a ha Ct Dt r

/-- **The core half with its cost bound** (the target). -/
structure S5CoreB2 (L : S5Lay Sw.nw) extends S5Core2 l F kclk coef A a ha Sw L where
  Cc : ℕ
  Dcc : ℕ
  cost_le : ∀ r, cost r ≤ s5Bound l F kclk coef A a ha Cc Dcc r

/-- **The halves in sequence** (one bridge step): within `s5Bound (Ct + Cc + 1) (max Dt Dcc)`. -/
theorem s5_cost_le2 (L : S5Lay Sw.nw) (T : S5ThrB2 l F kclk coef A a ha Sw L) (K : S5CoreB2 l F kclk coef A a ha Sw L)
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
