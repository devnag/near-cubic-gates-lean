import Proof.Wire_3_5.FinalPassSeams

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

/-! ## The per-point sums and the mask factor -/

section Point
variable (P : StarParams) {a : ℕ}

/-- **The THR per-point sum** `Σ_{g,p} R̂_{g,p}(c, u, v)` at the reporter `report`. -/
def rsumThr (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
    (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) (report : List Bool → ℕ) (c : BitInput P.n)
    (u v : P.Errors) : ℕ :=
  ∑ gp : ThrEq P Cs algorithm × PrimeIndex (thrCutoff P Cs algorithm den),
    (thrRhat P Cs algorithm den report gp.1 gp.2 c u v).toNat

/-- **The SYM per-point sum** `Σ_{e'} R̂_{e'}(c, u, v)` over the list seeds. -/
def rsumSym (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n) (Pl : FlatListParams) (c : BitInput P.n)
    (u v : P.Errors) : ℕ :=
  ∑ el : Pl.FlatSeed, (symRhatFast P Cs Pl el c u v).toNat

variable (σ : P.Translation) {N Q : ℕ} (eqv : P.Errors ≃ Fin N) (S : Fin Q → Fin N × Fin N)

/-- The THR point value is the mask times the per-point sum. -/
theorem ptThr_mask (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (FP : GapParams) (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) (report : List Bool → ℕ)
    (c : {c // P.IsCenter σ c}) (e : GapSeed FP) (l : Fin Q) :
    ptThr P σ eqv S Cs carriers FP algorithm den report c e l =
      (maskBits P σ carriers FP e (P.point c.1 (eqv.symm (S l).1) (eqv.symm (S l).2))).toNat *
        rsumThr P Cs algorithm den report c.1 (eqv.symm (S l).1) (eqv.symm (S l).2) := by
  unfold ptThr rsumThr
  rw [Finset.mul_sum]

/-- The SYM point value is the mask times the per-point sum. -/
theorem ptSym_mask (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (FP : GapParams) (Pl : FlatListParams) (c : {c // P.IsCenter σ c}) (e : GapSeed FP) (l : Fin Q) :
    ptSym P σ eqv S Cs carriers FP Pl c e l =
      (maskBits P σ carriers FP e (P.point c.1 (eqv.symm (S l).1) (eqv.symm (S l).2))).toNat *
        rsumSym P Cs Pl c.1 (eqv.symm (S l).1) (eqv.symm (S l).2) := by
  unfold ptSym rsumSym
  rw [Finset.mul_sum]

end Point

/-! ## The per-point evaluator's entry, exit and type -/

section Eval
variable {ns nr nw nn nsc nrs : ℕ} (S : Fin 3 ⊕ Fin nw ⊕ Fin nsc ↪ Fin (ns + 1))
  (R : Fin 1 ⊕ Fin nn ⊕ Fin nrs ↪ Fin nr)

/-- **The per-point entry**: the point framed on `S (inl 0..2)`, the call words `ws` on `S (inr (inl k))`, the
scratch streams `S (inr (inr j))` reading blank, all these heads at `0`; the numbers `vs` in `R (inr (inl i))`, the
accumulator `R (inl 0)` and the scratch registers `R (inr (inr j))` zero. -/
structure PtIn {n : ℕ} (c eu ev : BitInput n) (ws : Fin nw → List Bool) (vs : Fin nn → ℕ) (σ : WState ns nr) :
    Prop where
  ptC : σ.st (S (.inl 0)) = frame (List.ofFn c)
  ptU : σ.st (S (.inl 1)) = frame (List.ofFn eu)
  ptV : σ.st (S (.inl 2)) = frame (List.ofFn ev)
  wd : ∀ k, σ.st (S (.inr (.inl k))) = ws k
  sc : ∀ j, ∀ b ∈ σ.st (S (.inr (.inr j))), b = false
  heads : ∀ i, σ.sh (S i) = 0
  num : ∀ i, σ.val (R (.inr (.inl i))) = vs i
  acc : σ.val (R (.inl 0)) = 0
  zero : ∀ j, σ.val (R (.inr (.inr j))) = 0

/-- **The per-point exit**: the accumulator holds `v`; every head, every other register and the cell as at entry;
every stream outside the scratch unchanged; the scratch reading blank again. -/
structure PtOut (σ τ : WState ns nr) (v : ℕ) : Prop where
  val : τ.val = Function.update σ.val (R (.inl 0)) v
  sh : τ.sh = σ.sh
  cell : τ.cell = σ.cell
  st : ∀ i, (∀ j, i ≠ S (.inr (.inr j))) → τ.st i = σ.st i
  sc : ∀ j, ∀ b ∈ τ.st (S (.inr (.inr j))), b = false

end Eval

/-- **A per-point evaluator** of the value `val` over the calls `K` (S2 / S3 → S4): it declares its call words and
numbers; one word program per layout, with capacity and cost polynomial in `ptSize`, writes `val k c u v` into the
accumulator from every `PtIn` entry at the point `(c, u, v)` (the halves as error vectors, `e_L(u)`, `e_R(v)`). -/
structure PtEvalW (K : Type) (P : K → StarParams)
    (val : (k : K) → BitInput (P k).n → (P k).Errors → (P k).Errors → ℕ) where
  nw : ℕ
  nn : ℕ
  nsc : ℕ
  nrs : ℕ
  words : K → Fin nw → List Bool
  nums : K → Fin nn → ℕ
  prog : ∀ {ns nr : ℕ}, (Fin 3 ⊕ Fin nw ⊕ Fin nsc ↪ Fin (ns + 1)) → (Fin 1 ⊕ Fin nn ⊕ Fin nrs ↪ Fin nr) → WM ns nr
  need : ℕ → ℕ
  bound : ℕ → ℕ
  C : ℕ
  D : ℕ
  need_le : ∀ M, need M ≤ C * (M + 1) ^ D
  bound_le : ∀ M, bound M ≤ C * (M + 1) ^ D
  run : ∀ {ns nr : ℕ} (S : Fin 3 ⊕ Fin nw ⊕ Fin nsc ↪ Fin (ns + 1)) (R : Fin 1 ⊕ Fin nn ⊕ Fin nrs ↪ Fin nr)
    (k : K) (c : BitInput (P k).n) (u v : (P k).Errors) (cap : ℕ) (σ : WState ns nr),
    PtIn S R c ((P k).errorVector (P k).leftBlock u) ((P k).errorVector (P k).rightBlock v) (words k) (nums k) σ →
    need ((P k).n + (∑ i, (words k i).length) + ∑ i, nums k i) ≤ cap →
    ∃ τ, WExec cap (prog S R) σ τ (bound ((P k).n + (∑ i, (words k i).length) + ∑ i, nums k i)) ∧
      PtOut S R σ τ (val k c u v)

/-- The description size an evaluator's bounds are polynomial in: the point, the call words, the numbers. -/
def PtEvalW.ptSize {K : Type} {P : K → StarParams}
    {val : (k : K) → BitInput (P k).n → (P k).Errors → (P k).Errors → ℕ} (X : PtEvalW K P val) (k : K) : ℕ :=
  (P k).n + (∑ i, (X.words k i).length) + ∑ i, X.nums k i

/-- **The THR call data** a THR per-point evaluator sees: the tuple, the algorithm, the cutoff's `den`, and the
digit lists' data `D` (the reporter is `ListFast.listReportFast D`; at a call, the fixed hash's data). -/
structure ThrCall where
  P : StarParams
  a : ℕ
  ha : a ≤ 4
  Cs : Fin a → NormalizedThresholdThresholdCircuit P.n
  alg : RepairRepresentation.DecompositionAlgorithm
  den : ℕ
  D : ListData

/-- **The SYM call data** a SYM per-point evaluator sees: the tuple and the flat lists' parameters. -/
structure SymCall where
  P : StarParams
  a : ℕ
  ha : a ≤ 4
  Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n
  Pl : FlatListParams

/-- **S2's type**: the THR per-point evaluator of `Σ_{g,p} R̂_{g,p}`. -/
abbrev ThrPtEval : Type :=
  PtEvalW ThrCall (fun k => k.P) fun k c u v => rsumThr k.P k.Cs k.alg k.den (ListFast.listReportFast k.D) c u v

/-- **S3's type**: the SYM per-point evaluator of `Σ_{e'} R̂_{e'}`. -/
abbrev SymPtEval : Type :=
  PtEvalW SymCall (fun k => k.P) fun k c u v => rsumSym k.P k.Cs k.Pl c u v

/-! ## S5 → S4: the front's exit -/

section Family
variable (l : Literals) (F : GateFree l) (E₅ : Envelope) (c₅ kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The front's exit bank** (S5 → S4) at a layout `wd` (words), `nm` (numbers): at every request, the words
`ws r k` on tape `wd k`, the numbers `vs r i` in `W r`-bit binary on tape `nm i`, every other tape `j` all `false`
of length `bl r j` (S4's register tapes), every head at `0`. The words and numbers are the ones S2, S3 and S4
declare (`PtEvalW.words`, `PtEvalW.nums`, S4's own). -/
structure FrontOut {t nw nn : ℕ} (wd : Fin nw → Fin t) (nm : Fin nn → Fin t)
    (ws : FReq l F kclk coef A a ha → Fin nw → List Bool) (vs : FReq l F kclk coef A a ha → Fin nn → ℕ)
    (W : FReq l F kclk coef A a ha → ℕ) (bl : FReq l F kclk coef A a ha → Fin t → ℕ)
    (H : FReq l F kclk coef A a ha → Fin t → ℕ)
    (Ab : FReq l F kclk coef A a ha → Fin t → List Bool) : Prop where
  inj : ∀ k i, wd k ≠ nm i
  wdInj : Function.Injective wd
  nmInj : Function.Injective nm
  heads : ∀ r, H r = fun _ => 0
  words : ∀ r k, Ab r (wd k) = ws r k
  nums : ∀ r i, Ab r (nm i) = frame (binary (W r) (vs r i))
  numW : ∀ r i, vs r i < 2 ^ W r
  blank : ∀ r j, (∀ k, j ≠ wd k) → (∀ i, j ≠ nm i) → Ab r j = List.replicate (bl r j) false

/-! ## S6: the cost residual -/

/-- **The number of filter seeds** at a request. -/
noncomputable def seedCount (r : FReq l F kclk coef A a ha) : ℕ :=
  Fintype.card (GapSeed ((callInputs l F kclk coef A a ha).filterParams r.1.mode r.1.n))

/-- **The number of point evaluations** at a request: `|centers|·|filter seeds|·Q`. -/
def ptCountOf {kc : ℕ} {E : Envelope} {B : TimeBudget kc E} (I : PrimitiveInputs B)
    (alg : RepairRepresentation.DecompositionAlgorithm) : PrimRequest → ℕ
  | ⟨n, .sym, _, _, Cs, carriers, translation⟩ =>
      if hs : I.StarAt n then
        Fintype.card {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c} *
          Fintype.card (GapSeed (I.filterParams .sym n)) *
            ((SeedFix.greedySampler I alg).symS Cs carriers translation hs).Q
      else 0
  | ⟨n, .thr, _, _, Cs, carriers, translation⟩ =>
      if hs : I.StarAt n then
        Fintype.card {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c} *
          Fintype.card (GapSeed (I.filterParams .thr n)) *
            ((SeedFix.greedySampler I alg).thrS Cs carriers translation hs).Q
      else 0

/-- The number of point evaluations at a request of the family. -/
noncomputable abbrev ptCount (r : FReq l F kclk coef A a ha) : ℕ :=
  ptCountOf (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1

def seedsShape (nE tab nPt pt ov : ℕ) : ℕ := nE * tab + nPt * pt + ov

/-- **S6, the cost residual** (C6b): the phases' cost bounds fit `c₅·finalClasses` at every request. -/
def FitsRes (fB sB oB : FReq l F kclk coef A a ha → ℕ) : Prop :=
  ∀ r, fB r + 1 + (sB r + 1 + oB r) ≤ fpBudget l F E₅ c₅ kclk coef A a ha r

/-- **`fpPlan`'s `fits` from the residual**: phases within `fB`, `sB`, `oB`, and `FitsRes`. -/
theorem fits_of (X : FpPhases l F kclk coef A a ha) (fB sB oB : FReq l F kclk coef A a ha → ℕ)
    (hf : ∀ r, X.front.cost r ≤ fB r) (hs : ∀ r, X.seeds.cost r ≤ sB r) (ho : ∀ r, X.out.cost r ≤ oB r)
    (h : FitsRes l F E₅ c₅ kclk coef A a ha fB sB oB) :
    ∀ r, X.cost l F kclk coef A a ha r ≤ fpBudget l F E₅ c₅ kclk coef A a ha r := by
  intro r
  have h1 := hf r
  have h2 := hs r
  have h3 := ho r
  have h4 := h r
  unfold FpPhases.cost
  omega

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Seams
