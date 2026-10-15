import Proof.Foundations.SourceInterfaces
import StatementSupport

/-!
# Binding: HLW06 Construction 8.1 / Theorem 8.2 → `ExpanderSpectrumContract`

Source PDF: `HLW06_Hoory_Linial_Wigderson_Expander_Graphs.pdf` (quotations checked
against the rendered pages).

* PDF p.14 (printed 452), §2.1: "Unless we say otherwise, a graph G = (V,E) is undirected and
  d-regular (all vertices have the same degree d; that is each vertex is incident to exactly d
  edges). Self loops and multiple edges are allowed."
* PDF p.15 (printed 453), §2.3: "The Adjacency Matrix of an n-vertex graph G, denoted A = A(G),
  is an n × n matrix whose (u, v) entry is the number of edges in G between vertex u and vertex
  v. Being real and symmetric, the matrix A has n real eigenvalues which we denote by
  λ1 ≥ λ2 ≥ · · · ≥ λn."
* PDF p.16 (printed 454), §2.4: "Given a d-regular graph G with n vertices, we denote
  λ = λ(G) = max(|λ2|, |λn|). In words, λ is the largest absolute value of an eigenvalue other
  than λ1 = d."
* PDF p.65 (printed 503), Construction 8.1: "Define the following 8-regular graph Gn = G = (V,E)
  on the vertex set V = Zn × Zn. Let T1 = (1 2; 0 1), T2 = (1 0; 2 1), e1 = (1; 0),
  e2 = (0; 1). Each vertex v = (x, y) is adjacent to the four vertices T1v, T2v, T1v + e1,
  T2v + e2, and the other four neighbors of v obtained by the four inverse transformations.
  Note that all calculations are mod n and that this is an undirected 8-regular graph (that may
  have multiple edges and self loops)."
* PDF p.65, Theorem 8.2 (Gabber-Galil [GG81]): "The graph Gn satisfies λ(Gn) ≤ 5√2 < 8 for
  every positive integer n."

Transcription choices.
* `neighbor k v` lists the eight neighbours in HLW's order; the last four are the images of `v`
  under the INVERSES (`Equiv.symm`) of the four bijections `v ↦ T1v, T2v, T1v+e1, T2v+e2`; no
  inverse formula is written into the definition.
* `adjacency n u w` is "the number of edges between u and w": the multiplicity of `w` in the
  neighbour multiset of `u`. This is the reading under which the graph is 8-regular (each row sums
  to 8) with loops and multi-edges, as HLW say. It is symmetric (`adjacency_symm`), which is
  proved from the inverse-pairing alone.
* `λ1 ≥ … ≥ λn` are Mathlib's `IsHermitian.eigenvalues₀` (0-indexed, so HLW's `λi` is index
  `i - 1`). `eigenvalues₀_sorted_roots` records that this list IS the multiset of roots of the
  characteristic polynomial (the eigenvalues with multiplicity) sorted non-increasingly.
* `λ(G) = max(|λ2|, |λn|)` needs a second eigenvalue, so `hlwLambda` takes `2 ≤ |V|`. At
  `n = 1` (one vertex, eight loops), `λ2` does not exist and `λn = λ1 = 8 > 5√2`
  (`G1_eigenvalue`, `G1_naive_lambda_false`). A transcription that read `λ(G1)` as `|λn|` would
  make Theorem 8.2 FALSE at `n = 1`. HLW's words ("an eigenvalue other than λ1") give the empty
  maximum there. The literal therefore asserts the bound exactly when `λ2` exists, which is the
  weakest faithful reading. The import is vacuous at `m = 1` (a mean-zero vector on one vertex
  is zero), and the adapter handles that case separately.
* The adapter's linear algebra is Mathlib's spectral theorem (`IsHermitian.spectral_theorem`,
  `eigenvectorUnitary`, `eigenvalues₀_antitone`). No Courant–Fischer is needed. A mean-zero
  eigenvector has a nonzero coordinate on some eigenbasis index other than that of `λ1`, or else
  `λ1` equals the row sum `8` with multiplicity at least 2, so `λ2 = 8`. Also `|μ| ≤ 8` by the
  row-sum bound.
-/

namespace NearCubicWires.Bindings.HLW06

open NearCubicWires NearCubicWires.SourceInterfaces Matrix
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option warningAsError true
set_option maxRecDepth 120000

/-! ## Construction 8.1, literally -/

/-! ## The neighbour multiset is the import's `margulisNeighbor` multiset -/

theorem transformation_apply {n : ℕ} (i : Fin 4) (v : V n) :
    transformation i v = forward i v := rfl

theorem transformation_symm_apply {n : ℕ} (i : Fin 4) (v : V n) :
    (transformation i).symm v = backward i v := by
  rw [Equiv.symm_apply_eq, transformation_apply, forward_backward]

/-- Import label `k` ↦ HLW label. -/
def importLabel : Fin 8 → Fin 8 := ![0, 2, 4, 6, 1, 3, 5, 7]

def importLabelInv : Fin 8 → Fin 8 := ![0, 4, 1, 5, 2, 6, 3, 7]

def importLabelEquiv : Fin 8 ≃ Fin 8 where
  toFun := importLabel
  invFun := importLabelInv
  left_inv := by intro k; fin_cases k <;> rfl
  right_inv := by intro k; fin_cases k <;> rfl

theorem neighbor_importLabel {n : ℕ} [NeZero n] (k : Fin 8) (v : V n) :
    neighbor (importLabel k) v = margulisNeighbor k v := by
  fin_cases k <;>
    simp [neighbor, importLabel, margulisNeighbor, transformation_symm_apply,
      transformation_apply, forward, backward, act_T1, act_T2, e1, e2] <;>
    ring

/-- **(a) The labelled neighbour multiset of HLW's `G_n` equals the import's.** -/
theorem neighbors_eq_import {n : ℕ} [NeZero n] (v : V n) :
    neighbors v = Finset.univ.val.map fun k : Fin 8 => margulisNeighbor k v := by
  have hfun : (fun k : Fin 8 => margulisNeighbor k v) =
      (fun k : Fin 8 => neighbor k v) ∘ importLabelEquiv := by
    funext k
    exact (neighbor_importLabel k v).symm
  rw [hfun, ← Multiset.map_map, Multiset.map_univ_val_equiv]
  rfl

theorem sum_count_mul {W : Type*} [Fintype W] [DecidableEq W] (s : Multiset W) (f : W → ℝ) :
    ∑ w, (s.count w : ℝ) * f w = (s.map f).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    simp only [Multiset.count_cons, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      add_mul, Finset.sum_add_distrib, ih, Multiset.map_cons, Multiset.sum_cons, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring

/-- **(a) The adjacency matrices agree:** HLW's `A(G_n)` acting on a vector is the import's
`margulisAdjacency`. -/
theorem adjacency_mulVec {n : ℕ} [NeZero n] (f : V n → ℝ) (v : V n) :
    (adjacency n *ᵥ f) v = margulisAdjacency f v := by
  change ∑ w, adjacency n v w * f w = _
  unfold adjacency margulisAdjacency
  rw [sum_count_mul, neighbors_eq_import, Multiset.map_map]
  rfl

/-- Entry-wise form: HLW's `(u, w)` entry is the number of import labels `k` with
`margulisNeighbor k u = w`. -/
theorem adjacency_eq_import_count {n : ℕ} [NeZero n] (u w : V n) :
    adjacency n u w =
      ((Finset.univ.filter fun k : Fin 8 => w = margulisNeighbor k u).card : ℝ) := by
  unfold adjacency
  rw [neighbors_eq_import, Multiset.count_map]
  rfl

/-! ## Symmetry, from the inverse pairing alone -/

/-! ## HLW's `λ(G)`, literally -/

/-- The index list `λ1, …, λn` is non-increasing, as HLW write it. -/
theorem eigenvalues₀_sorted {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ)
    (hA : A.IsHermitian) : Antitone hA.eigenvalues₀ :=
  hA.eigenvalues₀_antitone

/-- The list `[λ1, …, λn]` is the multiset of roots of the characteristic polynomial (the
eigenvalues, with multiplicity) sorted non-increasingly. -/
theorem eigenvalues₀_sorted_roots {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ)
    (hA : A.IsHermitian) :
    List.ofFn hA.eigenvalues₀ = (A.charpoly.roots.map RCLike.re).sort (· ≥ ·) :=
  hA.sort_roots_charpoly_eq_eigenvalues₀.symm

/-! ## The edge `n = 1` -/

theorem card_V_one : Fintype.card (V 1) = 1 := by
  simp [V]

/-- At `n = 1` the single eigenvalue of `G_1` (one vertex, eight loops) is `8`, so
`λ1 = λn = 8`. -/
theorem G1_eigenvalue (i : Fin (Fintype.card (V 1))) :
    (adjacency_isHermitian 1).eigenvalues₀ i = 8 := by
  haveI : Subsingleton (V 1) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq card_V_one)
  have htr := (adjacency_isHermitian 1).trace_eq_sum_eigenvalues
  let v0 : V 1 := (0, 0)
  have hdiag : adjacency 1 v0 v0 = 8 := by
    unfold adjacency
    rw [Multiset.count_eq_card.mpr (fun x _ => Subsingleton.elim _ _)]
    simp [neighbors]
  have htrace : (adjacency 1).trace = 8 := by
    rw [Matrix.trace, Fintype.sum_subsingleton _ v0]
    exact hdiag
  rw [htrace, Fintype.sum_subsingleton _ v0] at htr
  have hidx : (Fintype.equivOfCardEq (Fintype.card_fin _)).symm v0 = i := by
    apply Fin.ext
    have h1 := ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm v0).isLt
    have h2 := i.isLt
    have hc := card_V_one
    omega
  have hev : (adjacency_isHermitian 1).eigenvalues v0 =
      (adjacency_isHermitian 1).eigenvalues₀ i := by
    rw [← hidx]
    rfl
  rw [← hev]
  simpa using htr.symm

/-- The naive reading `λ(G_1) = |λn|` would make Theorem 8.2 false at `n = 1`. -/
theorem G1_naive_lambda_false (i : Fin (Fintype.card (V 1))) :
    ¬ |(adjacency_isHermitian 1).eigenvalues₀ i| ≤ 5 * Real.sqrt 2 := by
  rw [G1_eigenvalue]
  intro h
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg 2
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 8)] at h
  nlinarith

/-! ## Linear algebra: a mean-zero eigenvalue is bounded by `λ(G)` -/

theorem five_sqrt_two_lt_eight : 5 * Real.sqrt 2 < 8 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg 2
  nlinarith

theorem abs_le_max_of_between {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    |b| ≤ max |a| |c| := by
  rw [abs_le]
  constructor
  · have h1 := neg_abs_le a
    have h2 := le_max_left |a| |c|
    linarith
  · have h1 := le_abs_self c
    have h2 := le_max_right |a| |c|
    linarith

/-- Every eigenvalue at an eigenbasis index other than that of `λ1` is bounded by `λ(G)`. -/
theorem abs_eigenvalue_le_hlwLambda {W : Type*} [Fintype W] [DecidableEq W]
    (A : Matrix W W ℝ) (hA : A.IsHermitian) (h2 : 2 ≤ Fintype.card W) (j : W)
    (hj : j ≠ Fintype.equivOfCardEq (Fintype.card_fin _) ⟨0, by omega⟩) :
    |hA.eigenvalues j| ≤ hlwLambda A hA h2 := by
  have hi : ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card W))).symm j).val ≠ 0 := by
    intro h0
    apply hj
    rw [← (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card W))).apply_symm_apply j]
    congr 1
    exact Fin.ext h0
  have hlo : (⟨1, by omega⟩ : Fin (Fintype.card W)) ≤
      (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card W))).symm j := by
    show 1 ≤ ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card W))).symm j).val
    omega
  have hhi : (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card W))).symm j ≤
      (⟨Fintype.card W - 1, by omega⟩ : Fin (Fintype.card W)) := by
    show ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card W))).symm j).val ≤
      Fintype.card W - 1
    have := ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card W))).symm j).isLt
    omega
  unfold hlwLambda
  rw [max_comm]
  exact abs_le_max_of_between (hA.eigenvalues₀_antitone hhi) (hA.eigenvalues₀_antitone hlo)

/-- **The linear-algebra step.** For a real symmetric `A` with constant row sum `d`, an
eigenvalue `μ` with a nonzero eigenvector orthogonal to the all-ones vector, and `|μ| ≤ |d|`,
satisfies `|μ| ≤ max(|λ2|, |λn|)`. -/
theorem abs_le_hlwLambda {W : Type*} [Fintype W] [DecidableEq W]
    (A : Matrix W W ℝ) (hA : A.IsHermitian) (h2 : 2 ≤ Fintype.card W) (d : ℝ)
    (hrow : A *ᵥ (fun _ => (1 : ℝ)) = d • (fun _ => (1 : ℝ)))
    (μ : ℝ) (f : W → ℝ) (hf : f ≠ 0) (hsum : ∑ w, f w = 0) (heig : A *ᵥ f = μ • f)
    (hμd : |μ| ≤ |d|) : |μ| ≤ hlwLambda A hA h2 := by
  set U : Matrix W W ℝ := (hA.eigenvectorUnitary : Matrix W W ℝ) with hUdef
  set D : Matrix W W ℝ := diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hDdef
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : A = U * D * star U := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hkey : star U * A = D * star U := by
    rw [hspec]
    calc star U * (U * D * star U) = (star U * U) * D * star U := by
          simp only [Matrix.mul_assoc]
      _ = D * star U := by rw [hUU, Matrix.one_mul]
  have hcoord : ∀ (x : W → ℝ) (c : ℝ), A *ᵥ x = c • x →
      ∀ j, hA.eigenvalues j * (star U *ᵥ x) j = c * (star U *ᵥ x) j := by
    intro x c hx j
    have h1 : D *ᵥ (star U *ᵥ x) = c • (star U *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, ← hkey, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]
    have h3 := congrFun h1 j
    rw [hDdef, Matrix.mulVec_diagonal] at h3
    simpa using h3
  have hrec : ∀ x : W → ℝ, U *ᵥ (star U *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, hUU', Matrix.one_mulVec]
  have hstarT : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have horth : ∀ x y : W → ℝ, (star U *ᵥ x) ⬝ᵥ (star U *ᵥ y) = x ⬝ᵥ y := by
    intro x y
    rw [Matrix.dotProduct_mulVec, hstarT, Matrix.mulVec_transpose, Matrix.vecMul_vecMul,
      ← hstarT, hUU', Matrix.vecMul_one]
  set g : W → ℝ := star U *ᵥ f with hgdef
  set h : W → ℝ := star U *ᵥ (fun _ : W => (1 : ℝ)) with hhdef
  have hg := hcoord f μ heig
  have hh := hcoord _ d hrow
  have hgne : g ≠ 0 := by
    intro hg0
    apply hf
    rw [← hrec f, ← hgdef, hg0, Matrix.mulVec_zero]
  have hhne : h ≠ 0 := by
    intro hh0
    have hone : (fun _ : W => (1 : ℝ)) = 0 := by
      rw [← hrec (fun _ : W => (1 : ℝ)), ← hhdef, hh0, Matrix.mulVec_zero]
    obtain ⟨w⟩ : Nonempty W := Fintype.card_pos_iff.mp (by omega)
    have := congrFun hone w
    simp at this
  have hgh : ∑ j, g j * h j = 0 := by
    have := horth f (fun _ => 1)
    rw [← hgdef, ← hhdef] at this
    simp only [dotProduct, mul_one] at this
    rw [this, hsum]
  by_cases hcase : ∃ j, j ≠ Fintype.equivOfCardEq (Fintype.card_fin _) ⟨0, by omega⟩ ∧ g j ≠ 0
  · obtain ⟨j, hj, hgj⟩ := hcase
    have hev : hA.eigenvalues j = μ := mul_right_cancel₀ hgj (hg j)
    rw [← hev]
    exact abs_eigenvalue_le_hlwLambda A hA h2 j hj
  · simp only [not_exists, not_and, not_not] at hcase
    set j₁ : W := Fintype.equivOfCardEq (Fintype.card_fin _) ⟨0, by omega⟩ with hj₁
    have hg1 : g j₁ ≠ 0 := by
      intro h0
      apply hgne
      funext j
      by_cases hj : j = j₁
      · rw [hj, h0]
        rfl
      · exact hcase j hj
    have hsingle : ∑ j, g j * h j = g j₁ * h j₁ :=
      Finset.sum_eq_single j₁ (fun j _ hj => by rw [hcase j hj, zero_mul]) (by simp)
    have hh1 : h j₁ = 0 := by
      have h0 := hgh
      rw [hsingle] at h0
      rcases mul_eq_zero.mp h0 with hz | hz
      · exact absurd hz hg1
      · exact hz
    obtain ⟨j, hj⟩ : ∃ j, h j ≠ 0 := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact hhne (funext hc)
    have hjne : j ≠ j₁ := by
      rintro rfl
      exact hj hh1
    have hev : hA.eigenvalues j = d := mul_right_cancel₀ hj (hh j)
    calc |μ| ≤ |d| := hμd
      _ = |hA.eigenvalues j| := by rw [hev]
      _ ≤ hlwLambda A hA h2 := abs_eigenvalue_le_hlwLambda A hA h2 j hjne

/-! ## The Margulis-graph facts the adapter needs -/

theorem adjacency_mulVec_eq {n : ℕ} [NeZero n] (f : V n → ℝ) :
    adjacency n *ᵥ f = fun v => margulisAdjacency f v :=
  funext fun v => adjacency_mulVec f v

theorem adjacency_row {n : ℕ} [NeZero n] :
    adjacency n *ᵥ (fun _ => (1 : ℝ)) = (8 : ℝ) • (fun _ => (1 : ℝ)) := by
  rw [adjacency_mulVec_eq]
  funext v
  simp [margulisAdjacency]

/-- Row-sum bound: an eigenvalue of the Margulis operator has `|μ| ≤ 8`. -/
theorem abs_margulis_eigenvalue_le_eight {n : ℕ} [NeZero n] (μ : ℝ) (f : V n → ℝ)
    (hf : ∃ v, f v ≠ 0) (heig : ∀ v, margulisAdjacency f v = μ * f v) : |μ| ≤ 8 := by
  obtain ⟨v, -, hv⟩ :=
    Finset.exists_max_image Finset.univ (fun w => |f w|) Finset.univ_nonempty
  have hpos : 0 < |f v| := by
    obtain ⟨w, hw⟩ := hf
    exact lt_of_lt_of_le (abs_pos.mpr hw) (hv w (Finset.mem_univ _))
  have hbound : |μ| * |f v| ≤ 8 * |f v| := by
    rw [← abs_mul, ← heig v]
    unfold margulisAdjacency
    calc |∑ k : Fin 8, f (margulisNeighbor k v)|
        ≤ ∑ k : Fin 8, |f (margulisNeighbor k v)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin 8, |f v| := Finset.sum_le_sum fun k _ => hv _ (Finset.mem_univ _)
      _ = 8 * |f v| := by simp
  exact le_of_mul_le_mul_right hbound hpos

/-- **Adapter.** The literal HLW06 Theorem 8.2 implies the imported
`SourceInterfaces.ExpanderSpectrumContract`. -/
theorem hlw06_to_import : HLW06_Theorem8_2 → ExpanderSpectrumContract := by
  intro hlit m _ μ hμ
  obtain ⟨f, ⟨v0, hv0⟩, hsum, heig⟩ := hμ
  refine ⟨?_, five_sqrt_two_lt_eight⟩
  by_cases h2 : 2 ≤ Fintype.card (V m)
  · refine le_trans ?_ (hlit m h2).1
    refine abs_le_hlwLambda (adjacency m) (adjacency_isHermitian m) h2 8 adjacency_row μ f
      ?_ hsum ?_ ?_
    · intro h0
      exact hv0 (congrFun h0 v0)
    · rw [adjacency_mulVec_eq]
      funext v
      rw [heig v]
      rfl
    · rw [abs_of_pos (by norm_num : (0 : ℝ) < 8)]
      exact abs_margulis_eigenvalue_le_eight μ f ⟨v0, hv0⟩ heig
  · exfalso
    haveI : Subsingleton (V m) := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    rw [Fintype.sum_subsingleton _ v0] at hsum
    exact hv0 hsum

end NearCubicWires.Bindings.HLW06
