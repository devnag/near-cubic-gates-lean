import SourceAdapters.Amplification.Layout
import SourceAdapters.Amplification.Interpolation

/-!
# Gate G-A: the rounded characteristic-two STV code, its layout, and the reduction to Theorem 29

The rounded characteristic-two layout and dyadic bound `ε/8 < δ ≤ ε/4` are used in
`app:sources`, "Full-range amplification interface".
 ("Full-range amplification interface"): the binary code family of [STV, Lemma 28] with the rounded
field and variable count, indexed by a product of binary cubes, of length a power of two, without padding.

For the dyadic accuracy `δ = 2^(-k-2)`, Theorem 29's constant `c` (any real with `c² ≤ C`), and a monic
irreducible `q ∈ 𝔽₂[X]` of degree `t = tParam C n k` (from the X3 search, `Joins/BinaryFieldArithmetic`):

* `stvEncode … msg : (Fin ℓ → Bool) → Bool`, `ℓ = (m+1)·t`, is the concatenated code of the truth table
  `msg : {0,1}^n → {0,1}`: the low-degree extension `innerPoly` of `msg` over `H^m ⊆ F^m` (STV Lemma 25, rounded),
  each symbol Hadamard-encoded (Lemma 28), laid out on `ℓ` bits by `layoutEquiv`;
* `innerPoly_degree`: total degree `≤ d = dParam n k`; `thm29_condition`: `c·√(d/|F|) < δ³` (strict);
* `innerPoly_recovers`: at the grid point of every `i ∈ {0,1}^n`, `innerPoly` takes the value `msg i`
  (`1` or `0` in `F`), so a procedure computing `innerPoly` at points recovers the truth table;
* **`gateA_decoding`**: every `g : {0,1}^ℓ → {0,1}` with agreement **more than** `1/2 + δ` with `stvEncode msg`
  yields a slot `j0 < ⌊1/δ²⌋` whose oracle `f = slot_{j0}(g)` — the `j0`-th Hadamard list element of each block of
  `g` — has agreement **at least** `δ³` with `innerPoly` (`STV.Agrees`), i.e. exactly Theorem 29's hypothesis at
  `ε = δ³`;
* `arity_le`: `ℓ ≤ (44 + size C)(n + k + 1)`; with `k ≤ n + 3` in the middle regime this is `O(n)`.

What remains after the gate (A02): apply the leaf `STV.Theorem29` to `f`, and compile the resulting oracle machine
with `f` realized from a circuit for `g` into a circuit for `msg` (with randomness fixed), with the size bound
`A(n/δ)^a s' + n + 2` of `app:sources`, "Full-range amplification interface".
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification

open Finset Polynomial NearCubicGates.Published.STV

variable (C n k : ℕ) {q : (ZMod 2)[X]} [Fact (Irreducible q)]

/-- The inner polynomial: the low-degree extension of the truth table `msg` over the grid. -/
noncomputable def innerPoly (q : (ZMod 2)[X]) [Fact (Irreducible q)] (msg : (Fin n → Bool) → Bool) :
    MvPolynomial (Fin (mParam n k)) (AdjoinRoot q) :=
  lde q (mParam n k) (hParam n k) (tParam C n k) (msgVal q msg)

/-- The inner codeword as words: the canonical `t`-bit word of `innerPoly` at each point of `F^m`. -/
noncomputable def innerWord (hq : q.Monic) (ht : q.natDegree = tParam C n k) (msg : (Fin n → Bool) → Bool)
    (z : Fin (mParam n k) → Fin (tParam C n k) → Bool) : Fin (tParam C n k) → Bool :=
  eltWord hq ht (evalAt q (innerPoly C n k q msg) z)

/-- **The rounded STV code** of the truth table `msg`, a Boolean function on `ℓ = (m+1)·t` bits. -/
noncomputable def stvEncode (hq : q.Monic) (ht : q.natDegree = tParam C n k) (msg : (Fin n → Bool) → Bool) :
    (Fin ((mParam n k + 1) * tParam C n k) → Bool) → Bool :=
  fun w => hadConcat (innerWord C n k hq ht msg) ((layoutEquiv _ _).symm w)

theorem hParam_le_tParam : hParam n k ≤ tParam C n k := by unfold tParam; omega

theorem innerPoly_degree (hq : q.Monic) (ht : q.natDegree = tParam C n k) (msg : (Fin n → Bool) → Bool) :
    (innerPoly C n k q msg).totalDegree ≤ dParam n k :=
  totalDegree_lde_le hq ht (hParam_le_tParam C n k) _

/-- **Recovery**: at the grid point of `i`, the inner polynomial is the bit `msg i`. -/
theorem innerPoly_recovers (hq : q.Monic) (ht : q.natDegree = tParam C n k) (msg : (Fin n → Bool) → Bool)
    (i : Fin n → Bool) :
    evalAt q (innerPoly C n k q msg)
        (fun j => hWord (t := tParam C n k) (grid (m := mParam n k) (h := hParam n k) i j)) =
      if msg i then 1 else 0 := by
  unfold evalAt innerPoly
  have := eval_lde_grid hq ht (hParam_le_tParam C n k) (msgVal (m := mParam n k) q msg)
    (grid (m := mParam n k) (h := hParam n k) i)
  rw [show (fun j => fieldElt q (hWord (t := tParam C n k) (grid (m := mParam n k) (h := hParam n k) i j))) =
      fun j => node q (t := tParam C n k) (grid (m := mParam n k) (h := hParam n k) i j) from rfl, this]
  exact msgVal_grid (le_mParam_mul n k) msg i

theorem dyadicAcc_lt_one (k : ℕ) : dyadicAcc k < 1 := by
  unfold dyadicAcc
  rw [div_lt_one (by positivity)]
  calc (1 : ℝ) < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)

/-- **Gate G-A, decoding half.** An adversary `g` with agreement more than `1/2 + δ` with the code yields a
Hadamard slot whose oracle has agreement at least `δ³` with the inner polynomial (Theorem 29's hypothesis). -/
theorem gateA_decoding (hq : q.Monic) (ht : q.natDegree = tParam C n k) (msg : (Fin n → Bool) → Bool)
    (g : (Fin ((mParam n k + 1) * tParam C n k) → Bool) → Bool)
    (hg : (1 / 2 + dyadicAcc k) * 2 ^ ((mParam n k + 1) * tParam C n k) <
      ((univ.filter fun w => g w = stvEncode C n k hq ht msg w).card : ℝ)) :
    ∃ j0 < ⌊1 / dyadicAcc k ^ 2⌋₊,
      Agrees q (fun z => slot (dyadicAcc k / 2) j0 (fun u => g (layoutEquiv _ _ (z, u))))
        (innerPoly C n k q msg) (dyadicAcc k ^ 3) := by
  have hcount := card_agree_layout (innerWord C n k hq ht msg) g
  have hdom := card_domain (mParam n k) (tParam C n k)
  have hagree : (1 / 2 + dyadicAcc k) *
      (Fintype.card (Fin (mParam n k) → Fin (tParam C n k) → Bool) * 2 ^ tParam C n k) <
      ∑ z, (agreeCount (fun u => g (layoutEquiv _ _ (z, u))) (innerWord C n k hq ht msg z) : ℝ) := by
    have e1 : ((Fintype.card (Fin (mParam n k) → Fin (tParam C n k) → Bool) * 2 ^ tParam C n k : ℕ) : ℝ) =
        (2 : ℝ) ^ ((mParam n k + 1) * tParam C n k) := by
      rw [hdom]; push_cast; ring
    push_cast at e1
    rw [e1]
    have h2 : ((univ.filter fun w => g w = stvEncode C n k hq ht msg w).card : ℝ) =
        ∑ z, (agreeCount (fun u => g (layoutEquiv _ _ (z, u))) (innerWord C n k hq ht msg z) : ℝ) := by
      have h3 : (univ.filter fun w => g w = stvEncode C n k hq ht msg w) =
          (univ.filter fun w => g w = hadConcat (innerWord C n k hq ht msg) ((layoutEquiv _ _).symm w)) := rfl
      rw [h3, hcount]; push_cast; rfl
    rw [← h2]; exact hg
  obtain ⟨j0, hj0, hbig⟩ := exists_good_slot (innerWord C n k hq ht msg)
    (fun z u => g (layoutEquiv _ _ (z, u))) (dyadicAcc k) (dyadicAcc_pos k) (dyadicAcc_lt_one k) hagree
  refine ⟨j0, hj0, ?_⟩
  unfold Agrees
  have hsub : (↑(univ.filter fun z => slot (dyadicAcc k / 2) j0 (fun u => g (layoutEquiv _ _ (z, u))) =
      innerWord C n k hq ht msg z) : Set (Fin (mParam n k) → Fin (tParam C n k) → Bool)) ⊆
      {x | fieldElt q (slot (dyadicAcc k / 2) j0 (fun u => g (layoutEquiv _ _ (x, u)))) =
        evalAt q (innerPoly C n k q msg) x} := by
    intro z hz
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hz
    simp only [Set.mem_setOf_eq]
    rw [hz]
    exact fieldElt_eltWord hq ht _
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset] at hle
  have hZ : (Fintype.card (Fin (mParam n k) → Fin (tParam C n k) → Bool) : ℝ) = 2 ^ (mParam n k * tParam C n k) := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    push_cast; rw [← pow_mul, mul_comm]
  rw [hZ] at hbig
  have hle' := (Nat.cast_le (α := ℝ)).mpr hle
  linarith

end NearCubicGates.Adapters.Amplification
