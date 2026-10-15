import Proof.Wire_3_5.FinalPassSeamsProg2

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.BlockPlatform NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.Split

section Family
variable (l : Literals) (F : GateFree l) (E₅ : Envelope) (c₅ kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The front's bound from PA2's halves**: the THR half then the core half, within `s5Bound`. -/
theorem front_dock (E3 : SymPtEval) (L : S5Lay E3.nw) (T : S5ThrB l F kclk coef A a ha E3 L)
    (K : S5CoreB l F kclk coef A a ha E3 L) (X : FpPhases l F kclk coef A a ha)
    (hf : ∀ r, X.front.cost r ≤ T.cost r + 1 + K.cost r) :
    ∀ r, X.front.cost r ≤ s5Bound l F kclk coef A a ha (T.Ct + K.Cc + 1) (max T.Dt K.Dcc) r :=
  fun r => (hf r).trans (s5_cost_le l F kclk coef A a ha E3 L T K r)

/-- **S6's dock**: at the front's `s5Bound`, the seeds phase's `SeedsProg2` bounds and the out machine's
`cost_le`, `FitsRes` gives `fpPlan`'s `fits`. -/
theorem fits_dock (X : FpPhases l F kclk coef A a ha) (Cf Df : ℕ) (Sw : SymWords)
    (S : SeedsProg2 l F kclk coef A a ha Sw) {t : ℕ} {o tN tD : Fin t} (O : OutMachine t o tN tD)
    (W : FReq l F kclk coef A a ha → ℕ)
    (hf : ∀ r, X.front.cost r ≤ s5Bound l F kclk coef A a ha Cf Df r)
    (hs : ∀ r, X.seeds.cost r ≤ seedsShape (seedCount l F kclk coef A a ha r) (S.tab r)
      (ptCount l F kclk coef A a ha r) (S.pt r) (S.ov r))
    (ho : ∀ r, X.out.cost r ≤ O.cost (W r))
    (h : FitsRes l F E₅ c₅ kclk coef A a ha (s5Bound l F kclk coef A a ha Cf Df)
      (fun r => seedsShape (seedCount l F kclk coef A a ha r) (s5Bound l F kclk coef A a ha S.Ct S.Dt r)
        (ptCount l F kclk coef A a ha r) (S.Cp * (r.1.n + 1) ^ S.Dp) (s5Bound l F kclk coef A a ha S.Co S.Do r))
      (fun r => O.C * (W r + 1) ^ O.D)) :
    ∀ r, X.cost l F kclk coef A a ha r ≤ fpBudget l F E₅ c₅ kclk coef A a ha r :=
  fits_of l F E₅ c₅ kclk coef A a ha X _ _ _ hf (fun r => (hs r).trans (S.cost_le l F kclk coef A a ha Sw r))
    (fun r => (ho r).trans (O.cost_le (W r))) h

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Seams
