import Proof.Wire_3_5.FinalPassSeamsProg

/-! # The per-point seam with a blank cell at entry

A word program has `setc` but no test of the result cell, and C5's majority machine (`majM_spec`) ends with an
existential cell, so `PtOut.cell` (the cell as at entry) is met by ending with `setc false` from an entry whose cell
is `false`. **`PtIn2`** is `PtIn` with `σ.cell = false`; **`PtEvalW2`** is `PtEvalW` whose run takes `PtIn2` (the exit
`PtOut` unchanged); `ThrPtEval2`, `SymPtEval2`, `PtEvalFix2` (words fixed), `PtEvalFix2.toW2`, `ThrPtProg2`. S4 sets
the cell to `false` before each point call. Paper quantities: as `PtEvalW` (the per-point sums `Σ R̂`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- **The per-point entry with a blank cell**: `PtIn` and `σ.cell = false`. -/
def PtIn2 {ns nr nw nn nsc nrs : ℕ} (S : Fin 3 ⊕ Fin nw ⊕ Fin nsc ↪ Fin (ns + 1))
    (R : Fin 1 ⊕ Fin nn ⊕ Fin nrs ↪ Fin nr) {n : ℕ} (c eu ev : BitInput n) (ws : Fin nw → List Bool)
    (vs : Fin nn → ℕ) (σ : WState ns nr) : Prop :=
  PtIn S R c eu ev ws vs σ ∧ σ.cell = false

/-- **A per-point evaluator from a blank cell** (`PtEvalW` with `PtIn2`). -/
structure PtEvalW2 (K : Type) (P : K → StarParams)
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
    PtIn2 S R c ((P k).errorVector (P k).leftBlock u) ((P k).errorVector (P k).rightBlock v) (words k) (nums k) σ →
    need ((P k).n + (∑ i, (words k i).length) + ∑ i, nums k i) ≤ cap →
    ∃ τ, WExec cap (prog S R) σ τ (bound ((P k).n + (∑ i, (words k i).length) + ∑ i, nums k i)) ∧
      PtOut S R σ τ (val k c u v)

/-- **S2's type, from a blank cell.** -/
abbrev ThrPtEval2 : Type :=
  PtEvalW2 ThrCall (fun k => k.P) fun k c u v => rsumThr k.P k.Cs k.alg k.den (ListFast.listReportFast k.D) c u v

/-- **S3's type, from a blank cell.** -/
abbrev SymPtEval2 : Type :=
  PtEvalW2 SymCall (fun k => k.P) fun k c u v => rsumSym k.P k.Cs k.Pl c u v

/-- **A per-point evaluator from a blank cell with its words fixed** (`PtEvalFix` with `PtIn2`). -/
structure PtEvalFix2 (K : Type) (P : K → StarParams)
    (val : (k : K) → BitInput (P k).n → (P k).Errors → (P k).Errors → ℕ) (nw nn : ℕ)
    (words : K → Fin nw → List Bool) (nums : K → Fin nn → ℕ) where
  nsc : ℕ
  nrs : ℕ
  prog : ∀ {ns nr : ℕ}, (Fin 3 ⊕ Fin nw ⊕ Fin nsc ↪ Fin (ns + 1)) → (Fin 1 ⊕ Fin nn ⊕ Fin nrs ↪ Fin nr) → WM ns nr
  need : ℕ → ℕ
  bound : ℕ → ℕ
  C : ℕ
  D : ℕ
  need_le : ∀ M, need M ≤ C * (M + 1) ^ D
  bound_le : ∀ M, bound M ≤ C * (M + 1) ^ D
  run : ∀ {ns nr : ℕ} (S : Fin 3 ⊕ Fin nw ⊕ Fin nsc ↪ Fin (ns + 1)) (R : Fin 1 ⊕ Fin nn ⊕ Fin nrs ↪ Fin nr)
    (k : K) (c : BitInput (P k).n) (u v : (P k).Errors) (cap : ℕ) (σ : WState ns nr),
    PtIn2 S R c ((P k).errorVector (P k).leftBlock u) ((P k).errorVector (P k).rightBlock v) (words k) (nums k) σ →
    need ((P k).n + (∑ i, (words k i).length) + ∑ i, nums k i) ≤ cap →
    ∃ τ, WExec cap (prog S R) σ τ (bound ((P k).n + (∑ i, (words k i).length) + ∑ i, nums k i)) ∧
      PtOut S R σ τ (val k c u v)

/-- Forget that the words are fixed. -/
def PtEvalFix2.toW2 {K : Type} {P : K → StarParams}
    {val : (k : K) → BitInput (P k).n → (P k).Errors → (P k).Errors → ℕ} {nw nn : ℕ}
    {words : K → Fin nw → List Bool} {nums : K → Fin nn → ℕ} (X : PtEvalFix2 K P val nw nn words nums) :
    PtEvalW2 K P val :=
  ⟨nw, nn, X.nsc, X.nrs, words, nums, X.prog, X.need, X.bound, X.C, X.D, X.need_le, X.bound_le, X.run⟩

/-- **S2's program type, from a blank cell**, at `thrWords`, `thrNums`. -/
abbrev ThrPtProg2 : Type :=
  PtEvalFix2 ThrCall (fun k => k.P)
    (fun k c u v => rsumThr k.P k.Cs k.alg k.den (ListFast.listReportFast k.D) c u v) 7 4 thrWords thrNums

/-- A `PtIn2` entry is a `PtIn` entry. -/
theorem PtIn2.pt {ns nr nw nn nsc nrs : ℕ} {S : Fin 3 ⊕ Fin nw ⊕ Fin nsc ↪ Fin (ns + 1)}
    {R : Fin 1 ⊕ Fin nn ⊕ Fin nrs ↪ Fin nr} {n : ℕ} {c eu ev : BitInput n} {ws : Fin nw → List Bool}
    {vs : Fin nn → ℕ} {σ : WState ns nr} (h : PtIn2 S R c eu ev ws vs σ) : PtIn S R c eu ev ws vs σ := h.1

/-- An old-style evaluator is one from a blank cell. -/
def PtEvalW.toW2 {K : Type} {P : K → StarParams}
    {val : (k : K) → BitInput (P k).n → (P k).Errors → (P k).Errors → ℕ} (X : PtEvalW K P val) : PtEvalW2 K P val :=
  ⟨X.nw, X.nn, X.nsc, X.nrs, X.words, X.nums, X.prog, X.need, X.bound, X.C, X.D, X.need_le, X.bound_le,
    fun S R k c u v cap σ h hc => X.run S R k c u v cap σ h.1 hc⟩

end NearCubicWires.WireExponent3_5.FinalPass.Seams
