import Proof.Wire_3_5.FinalPassSeamsProg2

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Split
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (Sw : SymWords)

/-- **S4's word layout.** -/
structure SdLay where
  ns : ℕ
  nr : ℕ
  wdS : Fin (17 + Sw.nw) → Fin (ns + 1)
  sN : Fin (ns + 1)
  sD : Fin (ns + 1)
  wdInj : Function.Injective wdS
  nd : sN ≠ sD
  wdN : ∀ k, wdS k ≠ sN
  wdD : ∀ k, wdS k ≠ sD

variable {Sw}

/-- **The internal entry** at a request, at width `W`. -/
structure SdEntry (L : SdLay Sw) (r : FReq l F kclk coef A a ha) (W : ℕ) (σ : WState L.ns L.nr) : Prop where
  words : ∀ k, σ.st (L.wdS k) = frontWordsW l F kclk coef A a ha Sw r k
  num : σ.st L.sN = frame (binary W 0)
  den : σ.st L.sD = frame (binary W (fpDen l F kclk coef A a ha r))
  blank : ∀ i, (∀ k, i ≠ L.wdS k) → i ≠ L.sN → i ≠ L.sD → σ.st i = []
  heads : ∀ i, σ.sh i = 0
  regs : ∀ q, σ.val q = 0
  cell : σ.cell = false

variable (Sw)

/-- **S4 at the word level** (BridgeT's input). -/
structure SeedsWM where
  L : SdLay Sw
  prog : WM L.ns L.nr
  Kc : ℕ
  Dc : ℕ
  tab : FReq l F kclk coef A a ha → ℕ
  pt : FReq l F kclk coef A a ha → ℕ
  ov : FReq l F kclk coef A a ha → ℕ
  Cp : ℕ
  Dp : ℕ
  Ct : ℕ
  Dt : ℕ
  Co : ℕ
  Do : ℕ
  pt_le : ∀ r : FReq l F kclk coef A a ha, pt r ≤ Cp * (r.1.n + 1) ^ Dp
  tab_le : ∀ r, tab r ≤ PrimAsm.S5Seam.s5Bound l F kclk coef A a ha Ct Dt r
  ov_le : ∀ r, ov r ≤ PrimAsm.S5Seam.s5Bound l F kclk coef A a ha Co Do r
  run : ∀ (r : FReq l F kclk coef A a ha) (W : ℕ), ptCount l F kclk coef A a ha r * vmax l F kclk coef A a ha r < 2 ^ W →
    ∀ σ : WState L.ns L.nr, SdEntry l F kclk coef A a ha L r W σ →
    ∃ τ, WExec (Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dc) prog σ τ
        (seedsShape (seedCount l F kclk coef A a ha r) (tab r) (ptCount l F kclk coef A a ha r) (pt r) (ov r)) ∧
      τ.st L.sN = frame (binary W (fpNum l F kclk coef A a ha r)) ∧
      τ.st L.sD = frame (binary W (fpDen l F kclk coef A a ha r)) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) ∧ fpNum l F kclk coef A a ha r < 2 ^ W

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Seams
