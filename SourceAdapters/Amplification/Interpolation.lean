import NineInputs
import Mathlib

/-!
# A01 step 2: the interpolation grid and the low-degree extension (STV Lemma 25, rounded)

STV text l.826–837 (proof of Lemma 25): "we pick a field F … and a subset H ⊆ F of cardinality (log k)/ε and set
m = (log k)/(log |H|). … Let b : [k] → H^m be any injective map. To encode a string x ∈ F^k, we find a polynomial
p̂ : F^m → F of degree at most |H| − 1 in each of the m variables satisfying p̂(b(i)) = x(i) for every i ∈ [k].
(Such a function does exist and can be found easily. The function may be made unique by forcing p̂(z) = 0 for all
z ∈ H^m \ image(b).)"

Here (`app:sources`, "Full-range amplification interface": the rounded construction) the field is `F = 𝔽₂[X]/(q)` with `q` monic of degree `t` and
elements the `t`-bit words of the leaf (`STV.fieldElt`, a bijection: `fieldElt_bijective`); `H` is the set of the
`2^h` words supported on the low `h` bits (`hWord`, `h ≤ t`); the message positions are the `n`-bit strings
`i ∈ {0,1}^n` (the truth table of the input function, `k = 2^n`), and `b = grid` cuts `i` into `m` blocks of `h`
bits (injective when `n ≤ m·h`, `grid_injective`). The extension `lde val = Σ_V val(V)·Π_j L_{V_j}(X_j)` (Lagrange
basis over `H`) has degree `≤ 2^h − 1` in each variable, total degree `≤ m(2^h − 1)` (`totalDegree_lde_le`), and
takes the value `val(V)` at every grid point `V ∈ H^m` (`eval_lde_grid`); with `val = 0` off the image of `grid`
(`msgVal`) it is STV's unique choice.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification

open Polynomial Finset NearCubicGates.Published.STV

/-! ## Field elements as words -/

theorem coeff_wordPoly {t : ℕ} (w : Fin t → Bool) (s : ℕ) :
    (wordPoly w).coeff s = if h : s < t then (if w ⟨s, h⟩ then 1 else 0) else 0 := by
  unfold wordPoly
  rw [finsetSum_coeff]
  by_cases hs : s < t
  · rw [dif_pos hs, Finset.sum_eq_single ⟨s, hs⟩]
    · by_cases hw : w ⟨s, hs⟩ <;> simp [hw]
    · intro b _ hb
      have : s ≠ b.val := fun h => hb (Fin.ext h.symm)
      by_cases hw : w b <;> simp [hw, coeff_X_pow, this]
    · simp
  · rw [dif_neg hs]
    apply Finset.sum_eq_zero
    intro b _
    have : s ≠ b.val := by have := b.isLt; omega
    by_cases hw : w b <;> simp [hw, coeff_X_pow, this]

theorem wordPoly_mem_degreeLT {t : ℕ} (w : Fin t → Bool) : wordPoly w ∈ degreeLT (ZMod 2) t := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero]
  intro s hs
  rw [coeff_wordPoly, dif_neg (by omega)]

theorem wordPoly_injective {t : ℕ} : Function.Injective (wordPoly (t := t)) := by
  intro w w' h
  funext s
  have h1 := congrArg (fun p => p.coeff s.val) h
  simp only [coeff_wordPoly, dif_pos s.isLt] at h1
  cases hw : w s <;> cases hw' : w' s <;> simp_all

/-- The leaf's representation is a bijection between `t`-bit words and `𝔽₂[X]/(q)` for `q` monic of degree `t`. -/
theorem fieldElt_bijective {q : (ZMod 2)[X]} {t : ℕ} (hq : q.Monic) (ht : q.natDegree = t) :
    Function.Bijective (fieldElt q : (Fin t → Bool) → AdjoinRoot q) := by
  constructor
  · intro w w' h
    unfold fieldElt at h
    rw [AdjoinRoot.mk_eq_mk] at h
    apply wordPoly_injective
    have hmem : wordPoly w - wordPoly w' ∈ degreeLT (ZMod 2) t :=
      Submodule.sub_mem _ (wordPoly_mem_degreeLT w) (wordPoly_mem_degreeLT w')
    rw [mem_degreeLT] at hmem
    have hdeg : (wordPoly w - wordPoly w').degree < q.degree := by
      rw [degree_eq_natDegree hq.ne_zero, ht]; exact hmem
    exact sub_eq_zero.mp (eq_zero_of_dvd_of_degree_lt h hdeg)
  · intro y
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
    set r := p %ₘ q
    have hr : r.degree < t := by
      have := degree_modByMonic_lt p hq
      rwa [degree_eq_natDegree hq.ne_zero, ht] at this
    refine ⟨fun s => decide (r.coeff s.val ≠ 0), ?_⟩
    unfold fieldElt
    rw [AdjoinRoot.mk_eq_mk]
    have hw : wordPoly (fun s : Fin t => decide (r.coeff s.val ≠ 0)) = r := by
      ext s
      rw [coeff_wordPoly]
      split_ifs with hs h2
      · simp only [decide_eq_true_eq] at h2
        have : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
        exact (this _ h2).symm
      · simp only [decide_eq_true_eq, not_not] at h2; exact h2.symm
      · exact (coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hr (by exact_mod_cast (not_lt.mp hs)))).symm
    rw [hw]
    have := modByMonic_add_div p q
    exact ⟨-(p /ₘ q), by linear_combination this⟩

/-- The canonical word of a field element. -/
noncomputable def eltWord {q : (ZMod 2)[X]} {t : ℕ} (hq : q.Monic) (ht : q.natDegree = t) (y : AdjoinRoot q) :
    Fin t → Bool :=
  (Equiv.ofBijective _ (fieldElt_bijective hq ht)).symm y

theorem fieldElt_eltWord {q : (ZMod 2)[X]} {t : ℕ} (hq : q.Monic) (ht : q.natDegree = t) (y : AdjoinRoot q) :
    fieldElt q (eltWord hq ht y) = y :=
  (Equiv.ofBijective _ (fieldElt_bijective hq ht)).apply_symm_apply y

/-! ## The grid `H^m` -/

/-- The words of `H`: supported on the low `h` of the `t` bits. -/
def hWord {h t : ℕ} (v : Fin h → Bool) : Fin t → Bool := fun s => if hs : s.val < h then v ⟨s.val, hs⟩ else false

theorem hWord_injective {h t : ℕ} (hht : h ≤ t) : Function.Injective (hWord (h := h) (t := t)) := by
  intro v v' heq
  funext s
  have := congrFun heq ⟨s.val, by omega⟩
  simpa [hWord, s.isLt] using this

/-- STV's injection `b : [k] → H^m`: the `n` index bits cut into `m` blocks of `h` bits (zero-filled). -/
def grid {n m h : ℕ} (i : Fin n → Bool) : Fin m → Fin h → Bool :=
  fun j s => if hp : j.val * h + s.val < n then i ⟨j.val * h + s.val, hp⟩ else false

theorem grid_injective {n m h : ℕ} (hnm : n ≤ m * h) : Function.Injective (grid (n := n) (m := m) (h := h)) := by
  intro i i' heq
  funext p
  have hh : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · rw [h0, Nat.mul_zero] at hnm; have := p.isLt; omega
    · exact h0
  have hj : p.val / h < m := by
    rw [Nat.div_lt_iff_lt_mul hh]; have := p.isLt; omega
  have hs : p.val % h < h := Nat.mod_lt _ hh
  have := congrFun (congrFun heq ⟨p.val / h, hj⟩) ⟨p.val % h, hs⟩
  have hp : p.val / h * h + p.val % h = p.val := by rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  simp only [grid, hp, dif_pos p.isLt] at this
  exact this

/-! ## The low-degree extension -/

variable {q : (ZMod 2)[X]} {h t : ℕ}

/-- The interpolation nodes: the elements of `H`. -/
noncomputable def node (q : (ZMod 2)[X]) {h t : ℕ} (v : Fin h → Bool) : AdjoinRoot q := fieldElt q (hWord (t := t) v)

theorem node_injective (hq : q.Monic) (hdeg : q.natDegree = t) (hht : h ≤ t) :
    Function.Injective (node q (h := h) (t := t)) :=
  (fieldElt_bijective hq hdeg).1.comp (hWord_injective hht)

/-- The Lagrange basis polynomial of the node `v` over `H`. -/
noncomputable def lagr (q : (ZMod 2)[X]) [Fact (Irreducible q)] (h t : ℕ) (v : Fin h → Bool) : (AdjoinRoot q)[X] :=
  Lagrange.basis univ (node q (h := h) (t := t)) v

/-- `Σ_V val(V)·Π_j L_{V_j}(X_j)`. -/
noncomputable def lde (q : (ZMod 2)[X]) [Fact (Irreducible q)] (m h t : ℕ)
    (val : (Fin m → Fin h → Bool) → AdjoinRoot q) : MvPolynomial (Fin m) (AdjoinRoot q) :=
  ∑ V : Fin m → Fin h → Bool, MvPolynomial.C (val V) * ∏ j, (lagr q h t (V j)).toMvPolynomial j

theorem totalDegree_toMvPolynomial_le {R : Type} [CommRing R] [Nontrivial R] {σ : Type} (p : R[X]) (i : σ) :
    (p.toMvPolynomial i).totalDegree ≤ p.natDegree := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  rw [map_mul, map_pow, Polynomial.toMvPolynomial_C, Polynomial.toMvPolynomial_X]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  have := Finset.mem_range.mp hk
  calc k * (MvPolynomial.X i : MvPolynomial σ R).totalDegree ≤ k * 1 :=
        Nat.mul_le_mul_left _ (MvPolynomial.totalDegree_X i).le
    _ ≤ p.natDegree := by omega

/-- **Degree**: `deg lde ≤ m(2^h − 1)`. -/
theorem totalDegree_lde_le [Fact (Irreducible q)] (hq : q.Monic) (hdeg : q.natDegree = t) (hht : h ≤ t) {m : ℕ}
    (val : (Fin m → Fin h → Bool) → AdjoinRoot q) :
    (lde q m h t val).totalDegree ≤ m * (2 ^ h - 1) := by
  unfold lde
  apply MvPolynomial.totalDegree_finsetSum_le
  intro V _
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc ∑ j, ((lagr q h t (V j)).toMvPolynomial j).totalDegree ≤ ∑ _j : Fin m, (2 ^ h - 1) := by
        apply Finset.sum_le_sum
        intro j _
        refine (totalDegree_toMvPolynomial_le _ _).trans ?_
        unfold lagr
        rw [Lagrange.natDegree_basis (fun a _ b _ hab => node_injective hq hdeg hht hab) (mem_univ _)]
        simp
    _ = m * (2 ^ h - 1) := by simp

/-- **Interpolation**: at a grid point `V' ∈ H^m`, `lde val` takes the value `val V'`. -/
theorem eval_lde_grid [Fact (Irreducible q)] (hq : q.Monic) (hdeg : q.natDegree = t) (hht : h ≤ t) {m : ℕ}
    (val : (Fin m → Fin h → Bool) → AdjoinRoot q) (V' : Fin m → Fin h → Bool) :
    MvPolynomial.eval (fun j => node q (t := t) (V' j)) (lde q m h t val) = val V' := by
  have hinj : Set.InjOn (node q (h := h) (t := t)) ↑(univ : Finset (Fin h → Bool)) :=
    fun a _ b _ hab => node_injective hq hdeg hht hab
  unfold lde
  rw [map_sum]
  simp_rw [map_mul, map_prod, MvPolynomial.eval_C, MvPolynomial.eval_toMvPolynomial]
  rw [Finset.sum_eq_single V']
  · rw [Finset.prod_eq_one]
    · ring
    · intro j _
      exact Lagrange.eval_basis_self hinj (mem_univ _)
  · intro V _ hV
    obtain ⟨j, hj⟩ : ∃ j, V j ≠ V' j := Function.ne_iff.mp hV
    rw [Finset.prod_eq_zero (mem_univ j)]
    · ring
    · exact Lagrange.eval_basis_of_ne hj (mem_univ _)
  · simp

/-- STV's message values: `x(i)` at the grid point `b(i)`, `0` off the image of `b`. -/
noncomputable def msgVal {n m h : ℕ} (q : (ZMod 2)[X]) (msg : (Fin n → Bool) → Bool)
    (V : Fin m → Fin h → Bool) : AdjoinRoot q := by
  classical
  exact if hV : ∃ i, grid i = V then (if msg hV.choose then 1 else 0) else 0

theorem msgVal_grid {n m h : ℕ} (hnm : n ≤ m * h) (msg : (Fin n → Bool) → Bool) (i : Fin n → Bool) :
    msgVal (m := m) (h := h) q msg (grid i) = if msg i then 1 else 0 := by
  classical
  have hex : ∃ i', grid (m := m) (h := h) i' = grid i := ⟨i, rfl⟩
  unfold msgVal
  rw [dif_pos hex]
  rw [grid_injective hnm hex.choose_spec]

end NearCubicGates.Adapters.Amplification
