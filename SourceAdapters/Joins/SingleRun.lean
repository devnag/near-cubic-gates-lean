import SourceAdapters.ShortPCP.Verifier
import SourceAdapters.ACSP.Affine
import Mathlib.LinearAlgebra.Lagrange

/-!
# Data and verdict of the single-run affine verifier

This module specifies the data and verdict of the proof of `thm:short-pcp-ours`, Step 2, and the
patched verifier of `lem:patch-r`. Step 4 compiles this exact ordinary run.

The request contains the affine constraint instance of `def:acsp`, the padded input, the H-test
parameter, and the patch masks. The instance word uses one input subspace and affine neighbor
pairs. The actual verifier uses the H-test parameter `d_H = 2^(f-2)` on the reduction's instances;
the request permits any supplied H-test parameter for the execution contract.
The parameter is separate from the existential weighted-degree certificate in `Instance.IsValid`.

The three proximity tests use single runs and prefixes of the same random string. The proof is
five field-element tables, bit-addressed in least-significant-first order. Missing coins are false.
The verdict accepts exactly when every test accepts on every supplied patch mask.

The execution contract in `Joins/SingleRunTime.lean` uses `frame data ++ frame R` and
promises correctness and runtime on `Request.Valid` inputs.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.Joins

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.LocalBitMultitape NearCubicWires.CanonicalBinary
open NearCubicGates.Published.BCGT13 NearCubicGates.Adapters.ShortPCP Polynomial

namespace SingleRun

/-- The fixed parameter tuple `(η, κ0, γ, μ) = (2, 4, 0, 1)` of BCGT13 Theorem 11.1. -/
def tuple0 : Tuple := ⟨2, 4, 0, 1⟩

/-- One request: the affine constraint instance, padded input, H-test degree parameter,
and patch masks. The singleton `[[]]` gives one unpatched run. -/
structure Request where
  code : NearCubicGates.Adapters.ACSP.Affine.Instance
  xbar : List Bool
  dB : ℕ
  masks : List (List Bool)

namespace Request

variable (q : Request)

/-- The data word (the compiler's `OracleCompilationRequest.data`). -/
def data : List Bool :=
  q.code.word ++ RepairOrdinary.frame q.xbar ++ natWord q.dB ++ listWord RepairOrdinary.frame q.masks

/-- The program input on coins `R`: exactly the compiler's `runInput` (`thm:short-pcp-ours`, Step 4). -/
def input (R : List Bool) : List Bool := RepairOrdinary.frame q.data ++ RepairOrdinary.frame R

/-- `m = log |x̄|`. -/
def mI : ℕ := Nat.log 2 q.xbar.length

/-- `d_A = 2^{mH} − 1`, the degree bound of the assignment (BCGT13 Def. 7.1, "degree less than `2^{mH}`"). -/
def dA : ℕ := 2 ^ q.code.hBasis.length - 1

/-- The execution hypotheses: the canonical instance is valid, and the padded input
has exactly the length specified by its positive-dimensional input subspace (`def:acsp`). -/
def Valid : Prop :=
  q.code.WellFormed ∧ q.code.IsValid ∧ q.xbar.length = 2 ^ q.code.m ∧ 1 ≤ q.code.m

section Field

variable {F : Type} [Field F] [DecidableEq F] (φ : AdjoinRoot (WireExponent3_5.GF.toPoly q.code.irr) →+* F)

/-- The field element of the word `a` (`GF.rep`). -/
def elt (a : ℕ) : F := φ (WireExponent3_5.GF.rep q.code.irr a)

/-- The domain `S = F`: basis `x^0, …, x^{f−1}` (words `2^j`), offset `0`. -/
def domBasis : List F := (List.range q.code.f).map fun j => q.elt φ (2 ^ j)

/-- `H_t`: basis and offset. -/
def hB : List F := q.code.hBasis.map (q.elt φ)
def hO : F := q.elt φ q.code.hOffset

/-- The single input subspace `I`: its basis and offset. -/
def iB : List F := q.code.iBasis.map (q.elt φ)
def iO : F := q.elt φ q.code.iOffset

/-- One gate, given the values `prior` of the earlier gates and the `m` inputs `env`; unknown indices read `0`. -/
def gateVal (m : ℕ) (env : ℕ → F) (prior : List F) : CodeGate → F
  | .input i => if i < m then env i else 0
  | .const v => q.elt φ v
  | .add a b => prior.getD a 0 + prior.getD b 0
  | .mul a b => prior.getD a 0 * prior.getD b 0

/-- The value of a straight-line circuit (its last gate, `0` if empty), using the constraint circuit's total zero-default semantics. -/
def circuitVal (m : ℕ) (env : ℕ → F) (gates : List CodeGate) : F :=
  (gates.foldl (fun prior g => prior ++ [q.gateVal φ m env prior g]) []).getLastD 0

/-- `px`: the low-degree extension of `x̄` over `I` (degree `< |x̄|`; its `i`-th point is GetEltWithIndex
`i + 1`), evaluated (BCGT13 Construction 8.5 Step 5; `thm:short-pcp-ours`, Step 2, "The instance"). -/
def px (α : F) : F :=
  (Lagrange.interpolate (Finset.range q.xbar.length) (fun i => eltWithIndex (q.iB φ) (q.iO φ) (i + 1))
    (fun i => if q.xbar.getD i false then 1 else 0)).eval α

/-- The instance as `ShortPCP.ACSPInstance`: neighbors are affine pairs, `P` is the constraint
circuit, and `dB` is the supplied H-test parameter. -/
def acsp : ACSPInstance F where
  H := span (q.hB φ) (q.hO φ)
  I := span (q.iB φ) (q.iO φ)
  cN := q.code.cN
  nbr i α := q.elt φ (q.code.nbr.getD i (0, 0)).1 * α +
    q.elt φ (q.code.nbr.getD i (0, 0)).2
  P α ys := q.circuitVal φ (q.code.cN + 1)
    (fun j => if h : j < q.code.cN + 1 then (Fin.cons α ys : Fin (q.code.cN + 1) → F) ⟨j, h⟩ else 0) q.code.cons
  dA := q.dA
  dB := q.dB
  px := q.px φ

/-- The three single-run sub-verifiers (BCGT13 Algorithms 13, 12, as transcribed in
`PublishedStatements/BCGT13.lean`), on the domain `S = F`. -/
def vR : FlatVerifier F := vRS tuple0 (q.domBasis φ) 0 q.dA
def vH : FlatVerifier F := vVRS tuple0 (q.domBasis φ) 0 (q.hB φ) (q.hO φ) q.dB
def vI : FlatVerifier F := vVRS tuple0 (q.domBasis φ) 0 (q.iB φ) (q.iO φ) q.dA

/-- BCGT13 Definition 8.4: "`π = (p0, π0, p1, π1, πc)`". -/
structure Table where
  p0 : F → F
  π0 : Fin (q.vR φ).length → F
  p1 : F → F
  π1 : Fin (q.vH φ).length → F
  πc : Fin (q.vI φ).length → F

/-- The point of the consistency test of Step 4: the first `f` coins read as a word (`thm:short-pcp-ours`,
Step 2). -/
def consistPoint (c : ℕ → Bool) : F := q.elt φ (bitsValue ((List.range q.code.f).map c))

/-- **`V0` on one coin sequence** (`thm:short-pcp-ours`, Step 2): Steps 2, 3, 4, 5 of Construction 8.5 with single
runs, each reading a prefix of `c`; `V0` "rejects whenever one of its steps rejects" (Step 2, "Base soundness"). -/
def runVerdict (pf : q.Table φ) (c : ℕ → Bool) : Bool :=
  (q.vR φ).accepts (q.domBasis φ) 0 pf.p0 pf.π0 (fun i => c i.val) &&
  (q.vH φ).accepts (q.domBasis φ) 0 pf.p1 pf.π1 (fun i => c i.val) &&
  consist (q.acsp φ) pf.p0 pf.p1 (q.consistPoint φ c) &&
  (q.vI φ).accepts (q.domBasis φ) 0 (fun a => pf.p0 a - (q.acsp φ).px a) pf.πc (fun i => c i.val)

/-- `R ⊕ σ`, missing bits read as `0`. -/
def maskedCoins (R σ : List Bool) (i : ℕ) : Bool := xor (R.getD i false) (σ.getD i false)

/-- **The patched verifier** (`lem:patch-r`): accept iff `V0` accepts on `R ⊕ σ` for every
`σ ∈ S`. -/
def patchedVerdict (pf : q.Table φ) (R : List Bool) : Bool :=
  q.masks.all fun σ => q.runVerdict φ pf (maskedCoins R σ)

/-! ### The binary proof (`thm:short-pcp-ours`, Step 2) -/

/-- The word of element `k` of the concatenated tables: oracle bits `k·f, …, k·f + f − 1`, least significant first. -/
def wordAt (o : ℕ → Bool) (k : ℕ) : ℕ :=
  bitsValue ((List.range q.code.f).map fun b => o (k * q.code.f + b))

/-- The word of a field element (`0` if none is below `2^f`; unique under `Valid`). -/
def wordOf (a : F) : ℕ := by
  classical
  exact if h : ∃ w, w < 2 ^ q.code.f ∧ q.elt φ w = a then Nat.find h else 0

/-- **The proof table read from an oracle** (layout `p0 | π0 | p1 | π1 | πc`, element offsets in field elements). -/
def decode (o : ℕ → Bool) : q.Table φ where
  p0 a := q.elt φ (q.wordAt o (q.wordOf φ a))
  π0 k := q.elt φ (q.wordAt o (2 ^ q.code.f + k.val))
  p1 a := q.elt φ (q.wordAt o (2 ^ q.code.f + (q.vR φ).length + q.wordOf φ a))
  π1 k := q.elt φ (q.wordAt o (2 * 2 ^ q.code.f + (q.vR φ).length + k.val))
  πc k := q.elt φ (q.wordAt o (2 * 2 ^ q.code.f + (q.vR φ).length + (q.vH φ).length + k.val))

/-- `L_π`: the number of proof bits (`thm:short-pcp-ours`, Step 2, "Randomness and length"). -/
def proofBits : ℕ :=
  (2 * 2 ^ q.code.f + (q.vR φ).length + (q.vH φ).length + (q.vI φ).length) * q.code.f

end Field

end Request

end SingleRun

end NearCubicGates.Adapters.Joins

end
