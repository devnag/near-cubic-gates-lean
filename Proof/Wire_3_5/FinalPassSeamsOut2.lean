import Proof.Wire_3_5.FinalPassAssemblyDock2

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.NumDen
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.BlockPlatform NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.Split

/-! ## The out machine from a blank output tape -/

/-- **The out machine, v2**: from every bank with `Num`, `Den` framed in `W`-bit binary on `tN`, `tD`, the output
tape `o` and the scratch tapes `sc` blank, and every head at `0`, it prints `ratWord (Num / Den)` on `o` with every
head back at `0`, within `cost W`. -/
structure OutMachine2 (t : ℕ) (o tN tD : Fin t) (sc : Fin t → Bool) where
  s : ℕ
  M : Machine t s
  cost : ℕ → ℕ
  C : ℕ
  D : ℕ
  cost_le : ∀ W, cost W ≤ C * (W + 1) ^ D
  exitA : (Fin t → List Bool) → ℕ → Fin t → List Bool
  run : ∀ (Ab : Fin t → List Bool) (W num den : ℕ), Ab tN = frame (binary W num) → Ab tD = frame (binary W den) →
    Ab o = [] → (∀ j, sc j = true → Ab j = []) → num < 2 ^ W → den < 2 ^ W → 0 < den →
    Step M (cost W) (fun _ => 0) Ab (fun _ => 0) (exitA Ab W) ∧ exitA Ab W o = ratWord ((num : ℚ) / den)

/-- **`FpPhases.out` from the out machine, v2**, at a seeds exit meeting `NumDenOut` with `o` and `sc` blank. -/
noncomputable def OutMachine2.phase {l : Literals} {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1} {t : ℕ}
    {o tN tD : Fin t} {sc : Fin t → Bool} (X : OutMachine2 t o tN tD sc) (W : FReq l F kclk coef A a ha → ℕ)
    (H : FReq l F kclk coef A a ha → Fin t → ℕ) (Ab : FReq l F kclk coef A a ha → Fin t → List Bool)
    (h : NumDenOut l F kclk coef A a ha tN tD W H Ab) (hb : ∀ r, Ab r o = [] ∧ ∀ j, sc j = true → Ab r j = []) :
    Phase (FReq l F kclk coef A a ha) t H Ab :=
  ⟨X.s, X.M, fun r => X.cost (W r), fun _ _ => 0, fun r => X.exitA (Ab r) (W r), fun r => by
    rw [h.heads r]
    exact (X.run (Ab r) (W r) _ _ (h.num r) (h.den r) (hb r).1 (hb r).2 (h.numW r) (h.denW r)
      (denOf_pos _ _ _)).1⟩

theorem OutMachine2.phase_out {l : Literals} {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1} {t : ℕ}
    {o tN tD : Fin t} {sc : Fin t → Bool} (X : OutMachine2 t o tN tD sc) (W : FReq l F kclk coef A a ha → ℕ)
    (H : FReq l F kclk coef A a ha → Fin t → ℕ) (Ab : FReq l F kclk coef A a ha → Fin t → List Bool)
    (h : NumDenOut l F kclk coef A a ha tN tD W H Ab) (hb : ∀ r, Ab r o = [] ∧ ∀ j, sc j = true → Ab r j = [])
    (r : FReq l F kclk coef A a ha) :
    (X.phase W H Ab h hb).H r = (fun _ => 0) ∧ (X.phase W H Ab h hb).A r o = fpOut l F kclk coef A a ha r := by
  refine ⟨rfl, ?_⟩
  rw [fpOut_eq]
  exact (X.run (Ab r) (W r) _ _ (h.num r) (h.den r) (hb r).1 (hb r).2 (h.numW r) (h.denW r) (denOf_pos _ _ _)).2

/-! ## The seeds phase keeping its idle tapes -/

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (Sw : SymWords)

/-- **The seeds phase, v4**: `SeedsProg3` with an idle set (no word, number or register tape) that its run keeps. -/
structure SeedsProg4 where
  t : ℕ
  wd : Fin (17 + Sw.nw) → Fin t
  tN : Fin t
  tD : Fin t
  reg : Fin t → Bool
  Kc : ℕ
  Dc : ℕ
  s : ℕ
  M : Machine t s
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
  idle : Fin t → Bool
  idleOff : ∀ j, idle j = true → reg j = false ∧ (∀ k, j ≠ wd k) ∧ j ≠ tN ∧ j ≠ tD
  exitA : (FReq l F kclk coef A a ha → Fin t → List Bool) → (FReq l F kclk coef A a ha → ℕ) →
    FReq l F kclk coef A a ha → Fin t → List Bool
  run : ∀ (H : FReq l F kclk coef A a ha → Fin t → ℕ) (Ab : FReq l F kclk coef A a ha → Fin t → List Bool)
    (W : FReq l F kclk coef A a ha → ℕ),
    FrontOut l F kclk coef A a ha wd ![tN, tD] (frontWordsW2 l F kclk coef A a ha Sw)
      (fun r => ![0, fpDen l F kclk coef A a ha r]) W
      (fun r j => if reg j then Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dc + 1 else 0) H Ab →
    (∀ r, ptCount l F kclk coef A a ha r * vmax l F kclk coef A a ha r < 2 ^ W r) →
    ∀ r, Step M (seedsShape (seedCount l F kclk coef A a ha r) (tab r) (ptCount l F kclk coef A a ha r) (pt r) (ov r))
        (H r) (Ab r) (fun _ => 0) (exitA Ab W r) ∧
      exitA Ab W r tN = frame (binary (W r) (fpNum l F kclk coef A a ha r)) ∧
      exitA Ab W r tD = frame (binary (W r) (fpDen l F kclk coef A a ha r)) ∧
      fpNum l F kclk coef A a ha r < 2 ^ W r ∧
      ∀ j, idle j = true → exitA Ab W r j = Ab r j

/-- The seeds phase's cost bound, v4. -/
theorem SeedsProg4.cost_le (X : SeedsProg4 l F kclk coef A a ha Sw) (r : FReq l F kclk coef A a ha) :
    seedsShape (seedCount l F kclk coef A a ha r) (X.tab r) (ptCount l F kclk coef A a ha r) (X.pt r) (X.ov r) ≤
      seedsShape (seedCount l F kclk coef A a ha r) (PrimAsm.S5Seam.s5Bound l F kclk coef A a ha X.Ct X.Dt r)
        (ptCount l F kclk coef A a ha r) (X.Cp * (r.1.n + 1) ^ X.Dp)
        (PrimAsm.S5Seam.s5Bound l F kclk coef A a ha X.Co X.Do r) := by
  unfold seedsShape
  have h1 := Nat.mul_le_mul_left (seedCount l F kclk coef A a ha r) (X.tab_le r)
  have h2 := Nat.mul_le_mul_left (ptCount l F kclk coef A a ha r) (X.pt_le r)
  have h3 := X.ov_le r
  omega

/-- **The idle tapes are blank at the front's exit.** -/
theorem idle_blank (X : SeedsProg4 l F kclk coef A a ha Sw) (H : FReq l F kclk coef A a ha → Fin X.t → ℕ)
    (Ab : FReq l F kclk coef A a ha → Fin X.t → List Bool) (W : FReq l F kclk coef A a ha → ℕ)
    (h : FrontOut l F kclk coef A a ha X.wd ![X.tN, X.tD] (frontWordsW2 l F kclk coef A a ha Sw)
      (fun r => ![0, fpDen l F kclk coef A a ha r]) W
      (fun r j => if X.reg j then X.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ X.Dc + 1 else 0) H Ab)
    (r : FReq l F kclk coef A a ha) (j : Fin X.t) (hj : X.idle j = true) : Ab r j = [] := by
  obtain ⟨hr, hw, hN, hD⟩ := X.idleOff j hj
  have e := h.blank r j hw (fun i => by
    match i with
    | ⟨0, _⟩ => exact hN
    | ⟨1, _⟩ => exact hD)
  rw [e, if_neg (by rw [hr]; decide)]
  rfl

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Seams

