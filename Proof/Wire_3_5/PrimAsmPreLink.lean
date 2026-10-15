import Proof.Wire_3_5.PrimAsmWriterIfaceJ

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.PreLink
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIfaceJ

theorem loadPsi_zero (k L BT BS : ℕ) : loadPsi 0 k L BT BS = 0 := by
  simp [loadPsi, loadThr, loadSym, loadAux]

/-- At `F.CD = 0` every call's load is `0`. -/
theorem psiOf_eq_zero (l : Literals) (F : GateFree l) (hF : F.CD = 0) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (n : ℕ) : ((gate0 l F).budget kclk coef A a ha).psiOf n = 0 := by
  unfold TimeBudget.psiOf
  have hCD : ((gate0 l F).budget kclk coef A a ha).CD = F.CD := rfl
  rw [hCD, hF, loadPsi_zero]

/-- At load `0` the preprocessing class is the polynomial `n^{Apre}`. -/
theorem preClass_zero (E : Envelope) (n k : ℕ) : classBound E .preprocessing n k 0 = n ^ E.Apre := by
  simp [classBound]

/-! ## The (e) TYPE -/

def PreLinkT (l : Literals) : Type :=
  ∀ fe D C : ℕ, Σ EW : Envelope, Σ CDW : ℕ, ∀ F : GateFree l, F.filterErrDeg = fe → ClassLE EW F.E → CDW ≤ F.CD →
    Σ' cW : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ),
      (callInputs l F kclk coef A a ha).StarAt n →
      C * (2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) + n + 1) ^ D ≤
        cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a ha).kOf n)
          (((gate0 l F).budget kclk coef A a ha).psiOf n)

/-! ## The writers' target with the floor -/

/-- **PA's (d) deliverable, v2 with the load-constant floor**: after `fe`, the writers' floors `E_W` and `CD_W`; for
every admissible `F` above both, a coefficient `c_W` and the three writers at every clock and source work
(SeedFixLeaf's order of choice; `WriterIfaceJ.WriterLeafJ` plus `CD_W ≤ F.CD`). -/
def WriterLeafJ2 (l : Literals) : Type :=
  ∀ fe : ℕ, Σ EW : Envelope, Σ CDW : ℕ, ∀ F : GateFree l, F.filterErrDeg = fe → ClassLE EW F.E → CDW ≤ F.CD →
    Σ cW : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), WritersAtJ l F EW cW kclk coef A a ha

/-- The old target gives the new one (the floor unused), so `WriterLeafJ2` is no stronger. -/
def WriterLeafJ.toJ2 {l : Literals} (W : WriterLeafJ l) : WriterLeafJ2 l :=
  fun fe => ⟨(W fe).1, 0, fun F hfe hle _ => (W fe).2 F hfe hle⟩

end NearCubicWires.WireExponent3_5.PrimAsm.PreLink
