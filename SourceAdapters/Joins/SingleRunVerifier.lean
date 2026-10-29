import SourceAdapters.Joins.SingleRun

/-!
# Join: the single-run verifier `V0` on an affine constraint instance

The verifier of Step 2 of the proof of `thm:short-pcp-ours`, on the affine constraint instance of `def:acsp`
(`ACSP/Affine.lean`, `Instance`). Consumers: its amplification (Step 3, `Joins/AmplifiedVerifier.lean`) and,
through it, the oracle circuit of Step 4.

`V0` is not defined again here. It is the verdict `Request.runVerdict` of `Joins/SingleRun.lean` (the three
single runs and the consistency test of Step 2, on the proof table that `Request.decode` reads from the proof bits),
on the request `request c x̄ S` whose H-test parameter is Step 2's `d_H`, over the field `F = 𝔽₂[X]/(irr)` itself
(`φ = id`). The time join `Joins/SingleRunTime.lean` states the running time of this same verdict.

Paper sentences stated here (proof of `thm:short-pcp-ours`, Step 2):
- "Let `V_0` be the verifier of [BCGT13, Construction 8.5] for `I_x`, with two changes. Each of the amplified
  proximity verifiers … is replaced by a single run of the corresponding strong proximity verifier …; and the test
  of `p_1` uses the degree bound `d_H` below"; "The test of `p_1` uses the degree bound `d_H = 2^{f−2} = |F|/4`, which
  `V_0` computes from `f` alone" — `dH`, `request`, `accepts`;
- "All steps read prefixes of one random string" and "`V_0` uses `r_0` random bits" — the coin clause;
- (a) "Randomness and length": "`r_0 ≤ f + 3 log(2f)`"; "the binary proof has `L_π` bits, where
  `L_π ≤ f(2·2^f + 3·16·2^f f^3) ≤ 64·2^f f^4`" — `r0` and `proofBits`, the counts of [BCGT13, Lemmas C.2–C.5] at
  the tuple `(η, κ_0, γ_rep, μ_rep) = (2, 4, 0, 1)` written as computations;
- (c) "Completeness": "So `V_0` accepts `π` with probability one";
- (d) "Base soundness": "it rejects `π` with probability at least `σ_0 = 1/(8 c_N (2 + K_f))`", with Step 3: "Choose
  fixed positive integers `K_1, b_1` such that `1/(K_1 f^{b_1}) ≤ σ_0`".

The instances on which the join speaks (`Good`) are those of Step 1: `def:acsp` (`Instance.IsValid`) in its
bit-level form (`Instance.WellFormed`), `|x̄| = 2^m` with `1 ≤ m < m_H`, `m_H + 2 ≤ f`, and `c_N ≤ K_c f`, the form of
`c_N = O(log T)` (`lem:acsp-degree`) that Step 3 uses. Each is a conjunct of `Joins.AffineConstraintReduction`.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.Joins

open NearCubicWires.WireExponent3_5 NearCubicGates.Published.BCGT13 NearCubicGates.Adapters.ShortPCP
open NearCubicGates.Adapters.ACSP.Affine

namespace SingleRun

/-! ## Numeric resources of the transcribed verifiers ([BCGT13, Lemmas C.2–C.5] as computations) -/

/-- Randomness of `vRS T B O d` for `|B| = κ` (the branches of `vRS` in `PublishedStatements/BCGT13.lean`). -/
def randRS (T : Tuple) (κ d : ℕ) : ℕ :=
  if κ ≤ T.η then 0
  else if d < dKE κ T.η then randEq T κ
  else if d = dKE κ T.η then randEq T κ
  else max (max (randEq T κ) (if mKED κ T.η d * (dKE κ T.η + 1) < d + 1 then randEq T κ else 0)) κ

/-- Proof length (field elements) of `vRS T B O d` for `|B| = κ`. -/
def lenRS (T : Tuple) (κ d : ℕ) : ℕ :=
  if κ ≤ T.η then 0
  else if d < dKE κ T.η then 2 * lengthEq T κ
  else if d = dKE κ T.η then lengthEq T κ
  else mKED κ T.η d * (2 ^ κ + lengthEq T κ) +
    (if mKED κ T.η d * (dKE κ T.η + 1) < d + 1 then 2 ^ κ + 2 * lengthEq T κ else 0)

/-- Randomness of `vVRS T B O BH OH d` for `|B| = κ`, `|BH| = h`. -/
def randVRS (T : Tuple) (κ h d : ℕ) : ℕ := max (randRS T κ (d - 2 ^ h)) κ

/-- Proof length of `vVRS T B O BH OH d` for `|B| = κ`, `|BH| = h`. -/
def lenVRS (T : Tuple) (κ h d : ℕ) : ℕ := 2 ^ κ + lenRS T κ (d - 2 ^ h)

/-! ## The parameters of `V0` on an instance -/

variable (c : Instance)

/-- Step 2: "The test of `p_1` uses the degree bound `d_H = 2^{f−2} = |F|/4`, which `V_0` computes from `f`
alone." -/
def dH : ℕ := 2 ^ (c.f - 2)

/-- `r_0` (Step 2 (a)): "As the steps share their random string", the largest of the four requirements: `V_RS` on
`p_0` (degree `2^{m_H} − 1`), `V_VRS` on `p_1` (subspace `H`, degree `d_H`), the `f` bits of the consistency test,
and `V_VRS` on `p_0 − A_x` (subspace `I`, degree `2^{m_H} − 1`), each on the domain `F` of dimension `f`. -/
def r0 : ℕ :=
  max (max (randRS tuple0 c.f (2 ^ c.mH - 1)) (randVRS tuple0 c.f c.mH (dH c)))
    (max c.f (randVRS tuple0 c.f c.m (2 ^ c.mH - 1)))

/-- The lengths (field elements) of the three proximity proofs `π_0`, `π_1`, `π_c`. -/
def len0 : ℕ := lenRS tuple0 c.f (2 ^ c.mH - 1)
def len1 : ℕ := lenVRS tuple0 c.f c.mH (dH c)
def lenC : ℕ := lenVRS tuple0 c.f c.m (2 ^ c.mH - 1)

/-- `L_π` (Step 2 (a)): two tables of `2^f` field elements and three proximity proofs, `f` bits per element. -/
def proofBits : ℕ := (2 * 2 ^ c.f + len0 c + len1 c + lenC c) * c.f

variable (xs : List Bool)

/-- The request on `(c, x̄)` with the mask list `S`: the instance, the padded input, and the H-test parameter
`d_H`. -/
def request (S : List (List Bool)) : Request := ⟨c, xs, dH c, S⟩

open Classical in
/-- **`V0`** (proof of `thm:short-pcp-ours`, Step 2) on the proof bits `π` and the random string `R` (bits beyond `R`
read `0`): `Request.runVerdict` over `F = 𝔽₂[X]/(irr)` with `φ = id` on the proof table read from `π`. It rejects
when `irr` is reducible, which `def:acsp` excludes. -/
def accepts (π : ℕ → Bool) (R : List Bool) : Bool :=
  if h : Irreducible c.irrPoly then
    haveI : Fact (Irreducible c.irrPoly) := ⟨h⟩
    letI : DecidableEq c.Fld := Classical.decEq _
    (request c xs [[]]).runVerdict (RingHom.id c.Fld) ((request c xs [[]]).decode (RingHom.id c.Fld) π)
      (fun i => R.getD i false)
  else false

/-- The instances of Step 1, on which the join speaks: the conjuncts of `Joins.AffineConstraintReduction` that the
verifier uses, with the `c_N` constant `Kc`. -/
structure Good (Kc : ℕ) (c : Instance) (xs : List Bool) : Prop where
  /-- The paragraph before `def:acsp`: "`F = F₂[X]/(irr)`, the field with `2^f` elements". -/
  wellFormed : c.WellFormed
  /-- `def:acsp`. -/
  valid : c.IsValid
  /-- Step 1: "`|x̄| = 2^m`". -/
  xbar_len : xs.length = 2 ^ c.m
  /-- Step 1: "its input subspace has dimension `lg |x̄|`, with `1 ≤ lg |x̄| ≤ τ_n < m_H`". -/
  one_le_m : 1 ≤ c.m
  m_lt : c.m < c.mH
  /-- Step 1: "`m_H + 2 ≤ f`". -/
  mH_two_le : c.mH + 2 ≤ c.f
  /-- `lem:acsp-degree` and Step 3: `c_N = O(log T)` in the form `c_N ≤ K_c f`. -/
  cN_le : c.cN ≤ Kc * c.f

end SingleRun

open SingleRun

/-- **The join.** For every `c_N` constant `Kc` there are fixed `K1, b1, K, b` such that on every instance satisfying
`Good`, the single-run verifier `V0` (`SingleRun.accepts`):
(c) accepts some proof on every random string when the instance accepts `x̄` (Step 2, "Completeness");
(d) accepts every proof with probability at most `1 − 1/(K1·f^{b1})` over its `r_0` random bits otherwise (Step 2,
    "Base soundness", and Step 3);
reads only the first `r_0` random bits and the first `L_π` proof bits; and has `r_0` and `L_π` as in Step 2 (a). -/
def SingleRunVerifier : Prop :=
  ∀ Kc : ℕ, ∃ K1 b1 K b : ℕ, 1 ≤ K1 ∧ ∀ (c : Instance) (xs : List Bool), Good Kc c xs →
    -- (c) Step 2, "Completeness": "every single run accepts on every random string. … So `V_0` accepts `π` with
    -- probability one"
    (c.Accepts xs → ∃ π : ℕ → Bool, ∀ R : List Bool, accepts c xs π R = true) ∧
    -- (d) Step 2, "Base soundness": "it rejects `π` with probability at least `σ_0`"; Step 3:
    -- "`1/(K_1 f^{b_1}) ≤ σ_0`"
    (¬ c.Accepts xs → ∀ π : ℕ → Bool,
      acceptFrac (fun R : Fin (r0 c) → Bool => accepts c xs π (List.ofFn R)) ≤
        1 - 1 / ((K1 : ℝ) * (c.f : ℝ) ^ b1)) ∧
    -- Step 2: "All steps read prefixes of one random string"; (a): "`V_0` uses `r_0` random bits"
    (∀ (π : ℕ → Bool) (R R' : List Bool), (∀ i < r0 c, R.getD i false = R'.getD i false) →
      accepts c xs π R = accepts c xs π R') ∧
    -- Step 2 (a): "the binary proof has `L_π` bits"
    (∀ π π' : ℕ → Bool, (∀ a < proofBits c, π a = π' a) → ∀ R : List Bool, accepts c xs π R = accepts c xs π' R) ∧
    -- Step 3: "The consistency test uses `f ≥ 1` random bits, so `r_0 ≥ 1`"; Step 2 (a): "`r_0 ≤ f + 3 log(2f)`"
    1 ≤ c.f ∧ c.f ≤ r0 c ∧ (r0 c : ℝ) ≤ c.f + 3 * Real.logb 2 (2 * c.f) ∧
    2 ^ r0 c ≤ K * 2 ^ c.f * c.f ^ b ∧
    -- Step 2 (a): "`L_π ≤ 64·2^f f^4`"
    proofBits c ≤ K * 2 ^ c.f * c.f ^ b

end NearCubicGates.Adapters.Joins
