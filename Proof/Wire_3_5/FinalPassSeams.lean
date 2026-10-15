import Proof.Wire_3_5.FinalPassNumDen
import Proof.Wire_3_5.FinalPassPlanFP

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

/-! ## Seeds → out -/

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- The numerator at a request of the family. -/
noncomputable abbrev fpNum (r : FReq l F kclk coef A a ha) : ℕ :=
  numOf (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1

/-- The denominator (`≥ 1`) at a request of the family. -/
noncomputable abbrev fpDen (r : FReq l F kclk coef A a ha) : ℕ :=
  denOf (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1

theorem fpOut_eq (r : FReq l F kclk coef A a ha) :
    fpOut l F kclk coef A a ha r = ratWord ((fpNum l F kclk coef A a ha r : ℚ) / fpDen l F kclk coef A a ha r) := by
  unfold fpOut; rw [value_eq]

/-- **The seeds phase's exit** (S4 → out): the numerator and the denominator framed in `W`-bit binary on `tN`, `tD`,
every head at `0`. -/
structure NumDenOut {t : ℕ} (tN tD : Fin t) (W : FReq l F kclk coef A a ha → ℕ)
    (H : FReq l F kclk coef A a ha → Fin t → ℕ) (Ab : FReq l F kclk coef A a ha → Fin t → List Bool) : Prop where
  ne : tN ≠ tD
  heads : ∀ r, H r = fun _ => 0
  num : ∀ r, Ab r tN = frame (binary (W r) (fpNum l F kclk coef A a ha r))
  den : ∀ r, Ab r tD = frame (binary (W r) (fpDen l F kclk coef A a ha r))
  numW : ∀ r, fpNum l F kclk coef A a ha r < 2 ^ W r
  denW : ∀ r, fpDen l F kclk coef A a ha r < 2 ^ W r

end Family

/-- **The out machine** (X6 at the tape level): from every bank with `Num`, `Den` framed in `W`-bit binary on `tN`,
`tD` and every head at `0`, it prints `ratWord (Num / Den)` on `o` with every head back at `0`, within `cost W`. -/
structure OutMachine (t : ℕ) (o tN tD : Fin t) where
  s : ℕ
  M : Machine t s
  cost : ℕ → ℕ
  C : ℕ
  D : ℕ
  cost_le : ∀ W, cost W ≤ C * (W + 1) ^ D
  exitA : (Fin t → List Bool) → ℕ → Fin t → List Bool
  run : ∀ (Ab : Fin t → List Bool) (W num den : ℕ), Ab tN = frame (binary W num) → Ab tD = frame (binary W den) →
    num < 2 ^ W → den < 2 ^ W → 0 < den →
    Step M (cost W) (fun _ => 0) Ab (fun _ => 0) (exitA Ab W) ∧ exitA Ab W o = ratWord ((num : ℚ) / den)

/-- **`FpPhases.out` from the out machine**, at any seeds exit meeting `NumDenOut`. -/
noncomputable def OutMachine.phase {l : Literals} {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1} {t : ℕ}
    {o tN tD : Fin t} (X : OutMachine t o tN tD) (W : FReq l F kclk coef A a ha → ℕ)
    (H : FReq l F kclk coef A a ha → Fin t → ℕ) (Ab : FReq l F kclk coef A a ha → Fin t → List Bool)
    (h : NumDenOut l F kclk coef A a ha tN tD W H Ab) : Phase (FReq l F kclk coef A a ha) t H Ab :=
  ⟨X.s, X.M, fun r => X.cost (W r), fun _ _ => 0, fun r => X.exitA (Ab r) (W r), fun r => by
    rw [h.heads r]
    exact (X.run (Ab r) (W r) _ _ (h.num r) (h.den r) (h.numW r) (h.denW r) (denOf_pos _ _ _)).1⟩

theorem OutMachine.phase_out {l : Literals} {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1} {t : ℕ}
    {o tN tD : Fin t} (X : OutMachine t o tN tD) (W : FReq l F kclk coef A a ha → ℕ)
    (H : FReq l F kclk coef A a ha → Fin t → ℕ) (Ab : FReq l F kclk coef A a ha → Fin t → List Bool)
    (h : NumDenOut l F kclk coef A a ha tN tD W H Ab) (r : FReq l F kclk coef A a ha) :
    (X.phase W H Ab h).H r = (fun _ => 0) ∧ (X.phase W H Ab h).A r o = fpOut l F kclk coef A a ha r := by
  refine ⟨rfl, ?_⟩
  rw [fpOut_eq]
  exact (X.run (Ab r) (W r) _ _ (h.num r) (h.den r) (h.numW r) (h.denW r) (denOf_pos _ _ _)).2

/-! ## The per-point value -/

section Point
variable (P : StarParams) (σ : P.Translation) {a : ℕ} {N Q : ℕ} (eqv : P.Errors ≃ Fin N)
  (S : Fin Q → Fin N × Fin N)

/-- **The THR per-point value** at center `c`, filter seed `e`, sample `ℓ`: `Σ_{g,p} M·R̂_{g,p}`. -/
def ptThr (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n) (carriers : List (Carrier P.n)) (FP : GapParams)
    (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) (report : List Bool → ℕ)
    (c : {c // P.IsCenter σ c}) (e : GapSeed FP) (l : Fin Q) : ℕ :=
  ∑ gp : ThrEq P Cs algorithm × PrimeIndex (thrCutoff P Cs algorithm den),
    (maskBits P σ carriers FP e (P.point c.1 (eqv.symm (S l).1) (eqv.symm (S l).2))).toNat *
      (thrRhat P Cs algorithm den report gp.1 gp.2 c.1 (eqv.symm (S l).1) (eqv.symm (S l).2)).toNat

theorem thrNum_pt (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (FP : GapParams) (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) (report : List Bool → ℕ) :
    thrNum P σ eqv S Cs carriers FP algorithm den report =
      ∑ c, ∑ e, ∑ l, ptThr P σ eqv S Cs carriers FP algorithm den report c e l := rfl

/-- **The SYM per-point value** at center `c`, filter seed `e`, sample `ℓ`: `Σ_{e'} M·R̂_{e'}` over the list seeds. -/
def ptSym (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n) (carriers : List (Carrier P.n)) (FP : GapParams)
    (Pl : FlatListParams) (c : {c // P.IsCenter σ c}) (e : GapSeed FP) (l : Fin Q) : ℕ :=
  ∑ el : Pl.FlatSeed,
    (maskBits P σ carriers FP e (P.point c.1 (eqv.symm (S l).1) (eqv.symm (S l).2))).toNat *
      (symRhatFast P Cs Pl el c.1 (eqv.symm (S l).1) (eqv.symm (S l).2)).toNat

theorem symNum_pt (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (FP : GapParams) (Pl : FlatListParams) :
    symNum P σ eqv S Cs carriers FP Pl = ∑ c, ∑ e, ∑ l, ptSym P σ eqv S Cs carriers FP Pl c e l := by
  unfold symNum ptSym
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Finset.sum_comm]

end Point

/-- **A per-point evaluator's result shape** (S2 THR / S3 SYM → S4): one word program; from every entry `Inp r e c l σ`
(the request's front words, seed `e`'s filter table, the point `(c, u_ℓ, v_ℓ)`), it adds `val r e c l` to the
accumulator register and changes nothing else, within a bound polynomial in the request's size. -/
structure PtEval {Req Seed Cen Smp : Type} (ns nr : ℕ) (Acc : Fin nr)
    (Inp : Req → Seed → Cen → Smp → WState ns nr → Prop) (val : Req → Seed → Cen → Smp → ℕ) (size : Req → ℕ) where
  prog : WM ns nr
  need : ℕ → ℕ
  bound : ℕ → ℕ
  C : ℕ
  D : ℕ
  need_le : ∀ M, need M ≤ C * (M + 1) ^ D
  bound_le : ∀ M, bound M ≤ C * (M + 1) ^ D
  run : ∀ (r : Req) (e : Seed) (c : Cen) (l : Smp) (σ : WState ns nr) (cap : ℕ), Inp r e c l σ → need (size r) ≤ cap →
    WExec cap prog σ (σ.setv Acc (σ.val Acc + val r e c l)) (bound (size r))

end NearCubicWires.WireExponent3_5.FinalPass.Seams
