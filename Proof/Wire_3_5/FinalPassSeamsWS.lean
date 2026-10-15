import Proof.Wire_3_5.FinalPassSeamsS4

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Split
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (Sw : SymWords)

/-- **S4 at the machine level** (BridgeT's input): one machine on the tapes of S4's word layout;
from `wenc` of every internal entry (`SdEntry`) with `ptCount·vmax < 2^W`, within `seedsShape`, it reaches `wenc` of
a state whose `sN` is `frame (binary W fpNum)`, `sD` unchanged, every head at `0`, every register `0`. -/
structure SeedsWS where
  L : SdLay Sw
  s : ℕ
  M : Machine (L.ns + 2 + L.nr) s
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
    ∃ τ : WState L.ns L.nr,
      Step M (seedsShape (seedCount l F kclk coef A a ha r) (tab r) (ptCount l F kclk coef A a ha r) (pt r) (ov r))
        (wenc (Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dc) σ).H
        (wenc (Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dc) σ).A
        (wenc (Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dc) τ).H
        (wenc (Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dc) τ).A ∧
      τ.st L.sN = frame (binary W (fpNum l F kclk coef A a ha r)) ∧
      τ.st L.sD = frame (binary W (fpDen l F kclk coef A a ha r)) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) ∧ fpNum l F kclk coef A a ha r < 2 ^ W

variable {l F kclk coef A a ha Sw}

/-- **A word-level S4 is a machine-level one**: its compiled program, `WExec.exec`, `Exec.step`. -/
noncomputable def SeedsWM.toWS (X : SeedsWM l F kclk coef A a ha Sw) : SeedsWS l F kclk coef A a ha Sw where
  L := X.L
  s := X.prog.toProg.size
  M := X.prog.toProg.compile
  Kc := X.Kc
  Dc := X.Dc
  tab := X.tab
  pt := X.pt
  ov := X.ov
  Cp := X.Cp
  Dp := X.Dp
  Ct := X.Ct
  Dt := X.Dt
  Co := X.Co
  Do := X.Do
  pt_le := X.pt_le
  tab_le := X.tab_le
  ov_le := X.ov_le
  run := fun r W hW σ hσ => by
    obtain ⟨τ, e, h1, h2, h3, h4, h5⟩ := X.run r W hW σ hσ
    exact ⟨τ, (WExec.exec _ e).step, h1, h2, h3, h4, h5⟩

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Seams
