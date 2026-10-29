import SourceAdapters.Joins.SingleRunVerifier

/-!
# Join: the amplified verifier `V1` on an affine constraint instance

The verifier of Step 3 of the proof of `thm:short-pcp-ours`. Consumer: the oracle circuit of Step 4. `V1` is the
patched verdict `Request.patchedVerdict` of `Joins/SingleRun.lean` on the request of
`Joins/SingleRunVerifier.lean` with the mask list `S` below; the time join `Joins/SingleRunTime.lean`
states the running time of this same verdict.

Paper sentences stated here (proof of `thm:short-pcp-ours`, Step 3, and `lem:patch-r`):
- "Choose the least nonnegative integer `m` such that `2^{2m} ≥ r_0^2 n K_1 f^{b_1}`, and use the powering
  construction in the proof of `lem:small-bias` over `𝔽_{2^m}`" — `target`, `mDeg`, `masks`;
- `lem:patch-r`: "Let `V` accept `x` with proof `π` and random string `R ∈ {0,1}^{r_0}` exactly when `V_0` accepts
  `x` with `π` and `R ⊕ σ` for every `σ ∈ S`" — `accepts`;
- "Since `n ≥ 2`, minimality of `m` gives `|S| = 2^{2m} < 4 r_0^2 n K_1 f^{b_1}`";
- "The resulting verifier `V_1` uses `r_0` random bits. It accepts the proof of (c) with probability one when `I_x`
  accepts `x̄`, and it accepts every proof with probability at most `1/n` otherwise."

The field `𝔽_{2^m}` is `𝔽₂[X]/(p)` with `p = GF.firstPrimitive m`, the modulus of the exhaustive search of
`Joins/BinaryFieldArithmetic.lean` (proof of `lem:small-bias`: "Find an irreducible polynomial of degree `m` over `𝔽₂`
by exhaustive search"). "For `a, b ∈ 𝔽_{2^m}` let `σ_{a,b} ∈ {0,1}^r` have coordinates `a^j · b`", where `·` is the
inner product over `𝔽₂` of the `m`-bit words of the two elements (`bdot`). The multiset is listed over the words
`a, b < 2^m`, with multiplicity.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.Joins

open NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ACSP.Affine

namespace SingleRun.Amplified

theorem exists_pow (N : ℕ) : ∃ m, N ≤ 2 ^ (2 * m) :=
  ⟨N, (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))⟩

/-- `r_0^2 · n · K_1 · f^{b_1}` (Step 3). -/
def target (c : Instance) (n K1 b1 : ℕ) : ℕ := r0 c ^ 2 * n * K1 * c.f ^ b1

/-- "the least nonnegative integer `m` such that `2^{2m} ≥ r_0^2 n K_1 f^{b_1}`" (Step 3). -/
def mDeg (N : ℕ) : ℕ := Nat.find (exists_pow N)

/-- The modulus of `𝔽_{2^m}`: the first primitive polynomial of degree `m` (`Joins/BinaryFieldArithmetic.lean`). -/
def modulus (m : ℕ) : ℕ := GF.firstPrimitive m

/-- The `m`-bit word of a field element: the least `a < 2^m` with `GF.rep p a = u` (`0` if there is none; under
`GF.ModulusOk p m` every element has exactly one). -/
def maskOf (p m : ℕ) (u : AdjoinRoot (GF.toPoly p)) : ℕ := by
  classical
  exact if h : ∃ a, a < 2 ^ m ∧ GF.rep p a = u then Nat.find h else 0

/-- The inner product over `𝔽₂` of the `m`-bit words of two field elements, in `𝔽₂`. -/
def dotZ (p m : ℕ) (u v : AdjoinRoot (GF.toPoly p)) : ZMod 2 :=
  ∑ i : Fin m, GF.bitF ((maskOf p m u).testBit i) * GF.bitF ((maskOf p m v).testBit i)

/-- The inner product `u · v ∈ {0, 1}` (proof of `lem:small-bias`). -/
def bdot (p m : ℕ) (u v : AdjoinRoot (GF.toPoly p)) : Bool := decide (dotZ p m u v = 1)

/-- `σ_{a,b}` for words `a, b < 2^m`: coordinates `a^j · b`, `0 ≤ j < r` (proof of `lem:small-bias`). -/
def sigma (m r a b : ℕ) : List Bool :=
  List.ofFn fun j : Fin r => bdot (modulus m) m (GF.rep (modulus m) a ^ j.val) (GF.rep (modulus m) b)

/-- The multiset `S` of the powering construction (Step 3), listed over the words (`|S| = 2^{2m}`). -/
def masks (c : Instance) (n K1 b1 : ℕ) : List (List Bool) :=
  let m := mDeg (target c n K1 b1)
  (List.range (2 ^ m)).flatMap fun a => (List.range (2 ^ m)).map fun b => sigma m (r0 c) a b

open Classical in
/-- **`V1`** (`lem:patch-r` with the multiset `S` of Step 3) on the proof bits `π` and the random string `R`:
`Request.patchedVerdict` on the request with the masks `S`, over `F = 𝔽₂[X]/(irr)` with `φ = id`, on the proof table
read from `π`. It rejects when `irr` is reducible, which `def:acsp` excludes. -/
def accepts (c : Instance) (xs : List Bool) (n K1 b1 : ℕ) (π : ℕ → Bool) (R : List Bool) : Bool :=
  if h : Irreducible c.irrPoly then
    haveI : Fact (Irreducible c.irrPoly) := ⟨h⟩
    letI : DecidableEq c.Fld := Classical.decEq _
    (request c xs (masks c n K1 b1)).patchedVerdict (RingHom.id c.Fld)
      ((request c xs (masks c n K1 b1)).decode (RingHom.id c.Fld) π) R
  else false

end SingleRun.Amplified

open SingleRun SingleRun.Amplified

/-- **The join.** For every `c_N` constant `Kc` there are fixed `K1, b1, K, b` (those of the single-run verifier) such
that for every instance satisfying `SingleRun.Good` and every `n ≥ 2`, the amplified verifier
`V1 = Amplified.accepts c x̄ n K1 b1`:
(c) accepts some proof on every random string when the instance accepts `x̄`;
(d) accepts every proof with probability at most `1/n` over its `r_0` random bits otherwise;
uses `|S| < 4·r_0^2·n·K1·f^{b1}` masks of `r_0` bits, reads only the first `r_0` random bits and the first `L_π`
proof bits, and has the single-run verifier's `r_0` and `L_π`. -/
def AmplifiedVerifier : Prop :=
  ∀ Kc : ℕ, ∃ K1 b1 K b : ℕ, 1 ≤ K1 ∧ ∀ (c : Instance) (xs : List Bool) (n : ℕ), Good Kc c xs → 2 ≤ n →
    -- Step 3: "It accepts the proof of (c) with probability one when `I_x` accepts `x̄`"
    (c.Accepts xs → ∃ π : ℕ → Bool, ∀ R : List Bool, Amplified.accepts c xs n K1 b1 π R = true) ∧
    -- Step 3: "and it accepts every proof with probability at most `1/n` otherwise"
    (¬ c.Accepts xs → ∀ π : ℕ → Bool,
      acceptFrac (fun R : Fin (r0 c) → Bool => Amplified.accepts c xs n K1 b1 π (List.ofFn R)) ≤ 1 / (n : ℝ)) ∧
    -- Step 3: "`|S| = 2^{2m} < 4 r_0^2 n K_1 f^{b_1}`"; each `σ ∈ {0,1}^{r_0}` (`lem:patch-r`)
    (masks c n K1 b1).length < 4 * target c n K1 b1 ∧
    (∀ σ ∈ masks c n K1 b1, σ.length = r0 c) ∧
    -- Step 3: "The resulting verifier `V_1` uses `r_0` random bits"
    (∀ (π : ℕ → Bool) (R R' : List Bool), (∀ i < r0 c, R.getD i false = R'.getD i false) →
      Amplified.accepts c xs n K1 b1 π R = Amplified.accepts c xs n K1 b1 π R') ∧
    -- Step 4: "its proof bits are read at addresses below `L_π`"
    (∀ π π' : ℕ → Bool, (∀ a < proofBits c, π a = π' a) → ∀ R : List Bool,
      Amplified.accepts c xs n K1 b1 π R = Amplified.accepts c xs n K1 b1 π' R) ∧
    -- the single-run verifier's resources (Step 2 (a))
    1 ≤ c.f ∧ c.f ≤ r0 c ∧ 2 ^ r0 c ≤ K * 2 ^ c.f * c.f ^ b ∧ proofBits c ≤ K * 2 ^ c.f * c.f ^ b

end NearCubicGates.Adapters.Joins
