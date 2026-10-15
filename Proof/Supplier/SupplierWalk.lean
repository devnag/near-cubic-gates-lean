import Proof.Foundations.SupplierPipeline

/-!
# Powered-walk amplification

The numerical fortieth-power bound and the finite union-bound portion of
Appendix A.11 are proved here.  Reversibility, self-adjointness, the
finite-dimensional spectral norm bound, the exact uniform transition operator,
the projection-operator multiple-hit estimate, and the resulting concrete
majority amplifier are all derived below.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.SupplierWalk

open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

/-! ## Reversibility and self-adjointness of the explicit walk -/

def margulisInverseLabel : Fin 8 → Fin 8 :=
  ![2, 3, 0, 1, 6, 7, 4, 5]

theorem margulisInverseLabel_involutive (label : Fin 8) :
    margulisInverseLabel (margulisInverseLabel label) = label := by
  fin_cases label <;> rfl

def margulisInverseLabelEquiv : Fin 8 ≃ Fin 8 where
  toFun := margulisInverseLabel
  invFun := margulisInverseLabel
  left_inv := margulisInverseLabel_involutive
  right_inv := margulisInverseLabel_involutive

theorem margulisNeighbor_inverse
    {m : ℕ} [NeZero m] (label : Fin 8)
    (vertex : MargulisVertex m) :
    margulisNeighbor (margulisInverseLabel label)
      (margulisNeighbor label vertex) = vertex := by
  fin_cases label <;> ext <;>
    simp [margulisInverseLabel, margulisNeighbor] <;> ring

def margulisNeighborEquiv {m : ℕ} [NeZero m] (label : Fin 8) :
    MargulisVertex m ≃ MargulisVertex m where
  toFun := margulisNeighbor label
  invFun := margulisNeighbor (margulisInverseLabel label)
  left_inv := margulisNeighbor_inverse label
  right_inv := by
    intro vertex
    have hinverse :=
      margulisNeighbor_inverse (margulisInverseLabel label) vertex
    simpa [margulisInverseLabel_involutive] using hinverse

theorem sum_margulisNeighbor
    {m : ℕ} [NeZero m] (label : Fin 8)
    (value : MargulisVertex m → ℝ) :
    ∑ vertex, value (margulisNeighbor label vertex) =
      ∑ vertex, value vertex := by
  exact Equiv.sum_comp (margulisNeighborEquiv label) value

theorem margulisAdjacency_sum
    {m : ℕ} [NeZero m] (value : MargulisVertex m → ℝ) :
    ∑ vertex, margulisAdjacency value vertex =
      8 * ∑ vertex, value vertex := by
  simp only [margulisAdjacency]
  rw [Finset.sum_comm]
  simp_rw [sum_margulisNeighbor]
  simp

theorem sum_mul_margulisNeighbor
    {m : ℕ} [NeZero m] (label : Fin 8)
    (left right : MargulisVertex m → ℝ) :
    ∑ vertex, left vertex * right (margulisNeighbor label vertex) =
      ∑ vertex,
        left (margulisNeighbor (margulisInverseLabel label) vertex) *
          right vertex := by
  let equivalence := margulisNeighborEquiv (m := m) label
  let value := fun vertex =>
    left (equivalence.symm vertex) * right vertex
  have hsum := Equiv.sum_comp equivalence value
  simpa [equivalence, value, margulisNeighborEquiv,
    margulisNeighbor_inverse] using hsum

theorem margulisAdjacency_symmetric
    {m : ℕ} [NeZero m]
    (left right : MargulisVertex m → ℝ) :
    ∑ vertex, left vertex * margulisAdjacency right vertex =
      ∑ vertex, margulisAdjacency left vertex * right vertex := by
  simp only [margulisAdjacency, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ label : Fin 8, ∑ vertex,
      left vertex * right (margulisNeighbor label vertex)) =
        ∑ label : Fin 8, ∑ vertex,
          left (margulisNeighbor (margulisInverseLabel label) vertex) *
            right vertex := by
      apply Finset.sum_congr rfl
      intro label _
      exact sum_mul_margulisNeighbor label left right
    _ = ∑ label : Fin 8, ∑ vertex,
          left (margulisNeighbor label vertex) * right vertex := by
      exact Equiv.sum_comp margulisInverseLabelEquiv
        (fun label : Fin 8 => ∑ vertex,
          left (margulisNeighbor label vertex) * right vertex)
    _ = ∑ vertex, ∑ label : Fin 8,
          left (margulisNeighbor label vertex) * right vertex :=
      Finset.sum_comm

theorem constant_margulisEigenvector
    {m : ℕ} [NeZero m] (constant : ℝ) (vertex : MargulisVertex m) :
    margulisAdjacency (fun _ => constant) vertex = 8 * constant := by
  simp [margulisAdjacency]

/-! ## Spectral contraction on the mean-zero subspace -/

noncomputable def margulisAdjacencyLinear {m : ℕ} [NeZero m] :
    Module.End ℝ (EuclideanSpace ℝ (MargulisVertex m)) where
  toFun := fun value => WithLp.toLp 2 (margulisAdjacency value.ofLp)
  map_add' := by
    intro left right
    apply WithLp.ofLp_injective
    funext vertex
    simp [margulisAdjacency, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar value
    apply WithLp.ofLp_injective
    funext vertex
    simp [margulisAdjacency, Finset.mul_sum]

theorem margulisAdjacencyLinear_isSymmetric
    {m : ℕ} [NeZero m] :
    LinearMap.IsSymmetric (𝕜 := ℝ)
      (margulisAdjacencyLinear (m := m)) := by
  intro left right
  change
    (∑ vertex, right.ofLp vertex *
      margulisAdjacency left.ofLp vertex) =
    ∑ vertex, margulisAdjacency right.ofLp vertex *
      left.ofLp vertex
  simpa [mul_comm] using
    (margulisAdjacency_symmetric left.ofLp right.ofLp).symm

noncomputable def coordinateSumLinear {m : ℕ} [NeZero m] :
    EuclideanSpace ℝ (MargulisVertex m) →ₗ[ℝ] ℝ where
  toFun := fun value => ∑ vertex, value.ofLp vertex
  map_add' := by
    intro left right
    simp [Finset.sum_add_distrib]
  map_smul' := by
    intro scalar value
    simp [Finset.mul_sum]

noncomputable def meanZeroSubmodule {m : ℕ} [NeZero m] :
    Submodule ℝ (EuclideanSpace ℝ (MargulisVertex m)) :=
  LinearMap.ker coordinateSumLinear

noncomputable def margulisAdjacencyMeanZero {m : ℕ} [NeZero m] :
    Module.End ℝ (meanZeroSubmodule (m := m)) where
  toFun := fun value => ⟨margulisAdjacencyLinear value.val, by
    change ∑ vertex, margulisAdjacency value.val.ofLp vertex = 0
    rw [margulisAdjacency_sum]
    have hzero : ∑ vertex, value.val.ofLp vertex = 0 := value.property
    rw [hzero, mul_zero]⟩
  map_add' := by
    intro left right
    apply Subtype.ext
    simp
  map_smul' := by
    intro scalar value
    apply Subtype.ext
    simp

theorem margulisAdjacencyMeanZero_isSymmetric
    {m : ℕ} [NeZero m] :
    LinearMap.IsSymmetric (𝕜 := ℝ)
      (margulisAdjacencyMeanZero (m := m)) := by
  intro left right
  exact margulisAdjacencyLinear_isSymmetric left.val right.val

theorem meanZero_eigenvalue_isNontrivial
    {m : ℕ} [NeZero m]
    (eigenvalue :
      Module.End.Eigenvalues (margulisAdjacencyMeanZero (m := m))) :
    IsNontrivialMargulisEigenvalue (m := m) eigenvalue.1 := by
  obtain ⟨vector, hvector⟩ :=
    Module.End.HasEigenvalue.exists_hasEigenvector eigenvalue.property
  refine ⟨vector.val.ofLp, ?_, ?_, ?_⟩
  · by_contra hallZero
    push Not at hallZero
    apply hvector.2
    apply Subtype.ext
    apply WithLp.ofLp_injective
    funext vertex
    exact hallZero vertex
  · exact vector.property
  · intro vertex
    have happly := hvector.apply_eq_smul
    have hvalues := congrArg
      (fun value : meanZeroSubmodule (m := m) =>
        value.val.ofLp vertex) happly
    simpa [margulisAdjacencyMeanZero, margulisAdjacencyLinear] using hvalues

theorem meanZero_eigenvalue_bound
    (spectrum : ExpanderSpectrumContract)
    {m : ℕ} [NeZero m]
    (eigenvalue :
      Module.End.Eigenvalues (margulisAdjacencyMeanZero (m := m))) :
    |eigenvalue.1| ≤ 5 * Real.sqrt 2 :=
  (spectrum m eigenvalue.1
    (meanZero_eigenvalue_isNontrivial eigenvalue)).1

theorem meanZero_eigenvalue_coe_eq
    {m : ℕ} [NeZero m]
    (eigenvalue :
      Module.End.Eigenvalues (margulisAdjacencyMeanZero (m := m))) :
    Module.End.Eigenvalues.val
      (margulisAdjacencyMeanZero (m := m)) eigenvalue =
        eigenvalue.1 := rfl

theorem symmetric_norm_le_of_eigenvalue_bound
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (operator : Module.End ℝ E)
    (hsymmetric : LinearMap.IsSymmetric (𝕜 := ℝ) operator)
    (bound : ℝ) (hboundNonnegative : 0 ≤ bound)
    (heigenvalues : ∀ eigenvalue : Module.End.Eigenvalues operator,
      |Module.End.Eigenvalues.val operator eigenvalue| ≤ bound)
    (value : E) :
    ‖operator value‖ ≤ bound * ‖value‖ := by
  let diagonalization := hsymmetric.diagonalization
  have hsquare :
      ‖operator value‖ ^ 2 ≤ (bound * ‖value‖) ^ 2 := by
    rw [← diagonalization.norm_map (operator value),
      ← diagonalization.norm_map value]
    rw [PiLp.norm_sq_eq_of_L2]
    dsimp only [diagonalization]
    simp_rw [hsymmetric.diagonalization_apply_self_apply]
    calc
      (∑ eigenvalue : Module.End.Eigenvalues operator,
          ‖(Module.End.Eigenvalues.val operator eigenvalue) •
            hsymmetric.diagonalization value eigenvalue‖ ^ 2) =
          ∑ eigenvalue : Module.End.Eigenvalues operator,
            |Module.End.Eigenvalues.val operator eigenvalue| ^ 2 *
              ‖hsymmetric.diagonalization value eigenvalue‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro eigenvalue _
        rw [norm_smul, Real.norm_eq_abs]
        ring
      _ ≤ ∑ eigenvalue : Module.End.Eigenvalues operator,
          bound ^ 2 *
            ‖hsymmetric.diagonalization value eigenvalue‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro eigenvalue _
        apply mul_le_mul_of_nonneg_right
        · exact (sq_le_sq₀ (abs_nonneg _)
            hboundNonnegative).2 (heigenvalues eigenvalue)
        · positivity
      _ = (bound * ‖hsymmetric.diagonalization value‖) ^ 2 := by
        rw [← Finset.mul_sum, ← PiLp.norm_sq_eq_of_L2]
        ring
  have hleft : 0 ≤ ‖operator value‖ := norm_nonneg _
  have hright : 0 ≤ bound * ‖value‖ :=
    mul_nonneg hboundNonnegative (norm_nonneg _)
  nlinarith

theorem margulisMeanZero_norm_bound
    (spectrum : ExpanderSpectrumContract)
    {m : ℕ} [NeZero m]
    (value : meanZeroSubmodule (m := m)) :
    ‖margulisAdjacencyMeanZero value‖ ≤
      (5 * Real.sqrt 2) * ‖value‖ := by
  apply symmetric_norm_le_of_eigenvalue_bound
    (margulisAdjacencyMeanZero (m := m))
    margulisAdjacencyMeanZero_isSymmetric
  · positivity
  · intro eigenvalue
    rw [meanZero_eigenvalue_coe_eq]
    exact meanZero_eigenvalue_bound spectrum eigenvalue

noncomputable def normalizedMargulisMeanZero {m : ℕ} [NeZero m] :
    Module.End ℝ (meanZeroSubmodule (m := m)) where
  toFun := fun value => (1 / 8 : ℝ) • margulisAdjacencyMeanZero value
  map_add' := by
    intro left right
    simp
  map_smul' := by
    intro scalar value
    simp [smul_smul, mul_comm]

theorem normalizedMargulisMeanZero_norm_bound
    (spectrum : ExpanderSpectrumContract)
    {m : ℕ} [NeZero m]
    (value : meanZeroSubmodule (m := m)) :
    ‖normalizedMargulisMeanZero value‖ ≤
      (5 * Real.sqrt 2 / 8) * ‖value‖ := by
  change ‖(1 / 8 : ℝ) • margulisAdjacencyMeanZero value‖ ≤
    (5 * Real.sqrt 2 / 8) * ‖value‖
  rw [norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 8)]
  have hbase := margulisMeanZero_norm_bound spectrum value
  calc
    (1 / 8 : ℝ) * ‖margulisAdjacencyMeanZero value‖ ≤
        (1 / 8 : ℝ) * ((5 * Real.sqrt 2) * ‖value‖) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = (5 * Real.sqrt 2 / 8) * ‖value‖ := by ring

theorem iterated_norm_le
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (operator : Module.End ℝ E) (bound : ℝ)
    (hboundNonnegative : 0 ≤ bound)
    (hoperator : ∀ value, ‖operator value‖ ≤ bound * ‖value‖)
    (iterations : ℕ) (value : E) :
    ‖(operator ^ iterations) value‖ ≤
      bound ^ iterations * ‖value‖ := by
  induction iterations with
  | zero =>
      simp
  | succ iterations inductionHypothesis =>
      rw [pow_succ']
      change ‖operator ((operator ^ iterations) value)‖ ≤
        bound ^ (iterations + 1) * ‖value‖
      calc
        ‖operator ((operator ^ iterations) value)‖ ≤
            bound * ‖(operator ^ iterations) value‖ :=
          hoperator _
        _ ≤ bound * (bound ^ iterations * ‖value‖) :=
          mul_le_mul_of_nonneg_left inductionHypothesis
            hboundNonnegative
        _ = bound ^ (iterations + 1) * ‖value‖ := by
          rw [pow_succ]
          ring

set_option maxRecDepth 20000 in
theorem poweredMargulisMeanZero_norm_bound
    (spectrum : ExpanderSpectrumContract)
    {m : ℕ} [NeZero m]
    (value : meanZeroSubmodule (m := m)) :
    ‖(normalizedMargulisMeanZero ^ 40) value‖ ≤
      (5 * Real.sqrt 2 / 8) ^ 40 * ‖value‖ := by
  exact iterated_norm_le
    (E := meanZeroSubmodule (m := m))
    normalizedMargulisMeanZero (5 * Real.sqrt 2 / 8)
    (by positivity)
    (normalizedMargulisMeanZero_norm_bound spectrum)
    40 value

/-! ## Exact finite-label transition averages -/

noncomputable def averageStep {Vertex Label : Type}
    [Fintype Vertex] [Fintype Label]
    (step : Label → Vertex → Vertex) :
    Module.End ℝ (EuclideanSpace ℝ Vertex) where
  toFun := fun value => WithLp.toLp 2 (fun vertex =>
    (∑ label, value.ofLp (step label vertex)) / Fintype.card Label)
  map_add' := by
    intro left right
    apply WithLp.ofLp_injective
    funext vertex
    simp [Finset.sum_add_distrib, add_div]
  map_smul' := by
    intro scalar value
    apply WithLp.ofLp_injective
    funext vertex
    change (∑ label, scalar * value.ofLp (step label vertex)) /
        Fintype.card Label =
      scalar * ((∑ label, value.ofLp (step label vertex)) /
        Fintype.card Label)
    rw [← Finset.mul_sum]
    ring

def tupleWalk {Vertex Label : Type}
    (step : Label → Vertex → Vertex) :
    {n : ℕ} → (Fin n → Label) → Vertex → Vertex
  | 0, _labels, vertex => vertex
  | _n + 1, labels, vertex =>
      tupleWalk step (Fin.tail labels) (step (labels 0) vertex)

lemma tupleWalk_cons {Vertex Label : Type}
    (step : Label → Vertex → Vertex)
    {n : ℕ} (head : Label) (tail : Fin n → Label) (vertex : Vertex) :
    tupleWalk step (Fin.cons head tail) vertex =
      tupleWalk step tail (step head vertex) := by
  rfl

set_option maxRecDepth 20000 in
theorem sum_tupleWalk
    {Vertex Label : Type} [Fintype Vertex] [Fintype Label]
    (step : Label → Vertex → Vertex)
    (hlabel : 0 < Fintype.card Label)
    (n : ℕ) (value : EuclideanSpace ℝ Vertex) (vertex : Vertex) :
    (∑ labels : Fin n → Label,
      value.ofLp (tupleWalk step labels vertex)) =
      (Fintype.card Label : ℝ) ^ n *
        ((averageStep step ^ n) value).ofLp vertex := by
  induction n generalizing vertex with
  | zero => simp [tupleWalk]
  | succ n ih =>
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 1) => Label)
        (fun labels => value.ofLp (tupleWalk step labels vertex))]
      simp only [Fintype.sum_prod_type]
      change (∑ head : Label, ∑ tail : Fin n → Label,
        value.ofLp (tupleWalk step (Fin.cons head tail) vertex)) = _
      simp_rw [tupleWalk_cons, ih]
      rw [← Finset.mul_sum]
      rw [pow_succ', pow_succ']
      change (Fintype.card Label : ℝ) ^ n *
          (∑ label : Label,
            ((averageStep step ^ n) value).ofLp (step label vertex)) =
        (Fintype.card Label : ℝ) * (Fintype.card Label : ℝ) ^ n *
          ((∑ label : Label,
            ((averageStep step ^ n) value).ofLp (step label vertex)) /
              Fintype.card Label)
      have hcard : (Fintype.card Label : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hlabel)
      field_simp

/-! The following generic finite-path recursion keeps the combinatorics
independent of the particular walk.  It is later instantiated with the
fortieth Margulis power, so uniform finite sums—not an ambient probability
library—justify the concrete transition experiment. -/

noncomputable def multiplyWeight {Vertex : Type} [Fintype Vertex]
    (weight : Vertex → ℝ) (value : EuclideanSpace ℝ Vertex) :
    EuclideanSpace ℝ Vertex :=
  WithLp.toLp 2 fun vertex => weight vertex * value.ofLp vertex

def finitePathWeight {Vertex Label : Type}
    (step : Label → Vertex → Vertex) :
    {n : ℕ} → (Fin (n + 1) → Vertex → ℝ) →
      Vertex → (Fin n → Label) → ℝ
  | 0, weights, start, _labels => weights 0 start
  | _n + 1, weights, start, labels =>
      weights 0 start *
        finitePathWeight step (fun time => weights time.succ)
          (step (labels 0) start) (Fin.tail labels)

noncomputable def finitePathValue {Vertex : Type} [Fintype Vertex]
    (operator : Module.End ℝ (EuclideanSpace ℝ Vertex)) :
    {n : ℕ} → (Fin (n + 1) → Vertex → ℝ) →
      EuclideanSpace ℝ Vertex
  | 0, weights => WithLp.toLp 2 (weights 0)
  | _n + 1, weights =>
      multiplyWeight (weights 0)
        (operator (finitePathValue operator
          (fun time => weights time.succ)))

set_option maxRecDepth 20000 in
theorem sum_finitePathWeight
    {Vertex Label : Type} [Fintype Vertex] [Fintype Label]
    (step : Label → Vertex → Vertex)
    (operator : Module.End ℝ (EuclideanSpace ℝ Vertex))
    (htransition : ∀ value vertex,
      (∑ label : Label, value.ofLp (step label vertex)) =
        Fintype.card Label * (operator value).ofLp vertex)
    (n : ℕ) (weights : Fin (n + 1) → Vertex → ℝ)
    (start : Vertex) :
    (∑ labels : Fin n → Label,
      finitePathWeight step weights start labels) =
      (Fintype.card Label : ℝ) ^ n *
        (finitePathValue operator weights).ofLp start := by
  induction n generalizing start with
  | zero =>
      classical
      rw [show (Finset.univ : Finset (Fin 0 → Label)) =
          {fun index => Fin.elim0 index} by
        ext labels
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        exact Subsingleton.elim _ _]
      simp only [Finset.sum_singleton]
      change weights 0 start = (1 : ℝ) * weights 0 start
      ring
  | succ n ih =>
      rw [← Equiv.sum_comp
        (Fin.consEquiv fun _ : Fin (n + 1) => Label)
        (fun labels => finitePathWeight step weights start labels)]
      simp only [Fintype.sum_prod_type]
      change (∑ head : Label, ∑ tail : Fin n → Label,
        weights 0 start *
          finitePathWeight step (fun time => weights time.succ)
            (step head start) tail) = _
      simp_rw [← Finset.mul_sum]
      simp_rw [ih]
      rw [← Finset.mul_sum]
      rw [htransition]
      rw [show (Fintype.card Label : ℝ) ^ (n + 1) =
        (Fintype.card Label : ℝ) *
          (Fintype.card Label : ℝ) ^ n by rw [pow_succ']]
      simp only [finitePathValue, multiplyWeight]
      change weights 0 start *
          ((Fintype.card Label : ℝ) ^ n *
            ((Fintype.card Label : ℝ) *
              (operator
                (finitePathValue operator
                  fun time => weights time.succ)).ofLp start)) =
        (Fintype.card Label : ℝ) *
          (Fintype.card Label : ℝ) ^ n *
            (weights 0 start *
              (operator
                (finitePathValue operator
                  fun time => weights time.succ)).ofLp start)
      ring

def finitePathNat {Vertex Label : Type}
    (step : Label → Vertex → Vertex)
    {n : ℕ} (start : Vertex) (labels : Fin n → Label) :
    (time : ℕ) → time ≤ n → Vertex
  | 0, _ => start
  | time + 1, htime =>
      step (labels ⟨time, by omega⟩)
        (finitePathNat step start labels time (by omega))

def finitePathVertex {Vertex Label : Type}
    (step : Label → Vertex → Vertex)
    {n : ℕ} (start : Vertex) (labels : Fin n → Label)
    (time : Fin (n + 1)) : Vertex :=
  finitePathNat step start labels time.val (by omega)

@[simp] theorem finitePathVertex_zero
    {Vertex Label : Type} (step : Label → Vertex → Vertex)
    {n : ℕ} (start : Vertex) (labels : Fin n → Label) :
    finitePathVertex step start labels 0 = start := by
  rfl

@[simp] theorem finitePathVertex_succ
    {Vertex Label : Type} (step : Label → Vertex → Vertex)
    {n : ℕ} (start : Vertex) (labels : Fin n → Label)
    (time : Fin n) :
    finitePathVertex step start labels time.succ =
      step (labels time)
        (finitePathVertex step start labels time.castSucc) := by
  change finitePathNat step start labels (time.val + 1) _ = _
  simp only [finitePathNat]
  congr

theorem finitePathNat_tail
    {Vertex Label : Type} (step : Label → Vertex → Vertex)
    {n : ℕ} (start : Vertex) (labels : Fin (n + 1) → Label)
    (time : ℕ) (htime : time ≤ n) :
    finitePathNat step (step (labels 0) start) (Fin.tail labels)
        time htime =
      finitePathNat step start labels (time + 1) (by omega) := by
  induction time with
  | zero => rfl
  | succ time ih =>
      simp only [finitePathNat]
      congr
      exact ih (by omega)

theorem finitePathVertex_tail
    {Vertex Label : Type} (step : Label → Vertex → Vertex)
    {n : ℕ} (start : Vertex) (labels : Fin (n + 1) → Label)
    (time : Fin (n + 1)) :
    finitePathVertex step (step (labels 0) start) (Fin.tail labels) time =
      finitePathVertex step start labels time.succ := by
  apply finitePathNat_tail

theorem finitePathWeight_eq_product
    {Vertex Label : Type}
    (step : Label → Vertex → Vertex)
    (n : ℕ) (weights : Fin (n + 1) → Vertex → ℝ)
    (start : Vertex) (labels : Fin n → Label) :
    finitePathWeight step weights start labels =
      ∏ time : Fin (n + 1),
        weights time (finitePathVertex step start labels time) := by
  induction n generalizing start with
  | zero =>
      rw [Fin.prod_univ_succ]
      rw [finitePathVertex_zero]
      simp only [finitePathWeight]
      simp
  | succ n ih =>
      rw [Fin.prod_univ_succ]
      rw [finitePathVertex_zero]
      simp only [finitePathWeight]
      change weights 0 start *
          finitePathWeight step (fun time => weights time.succ)
            (step (labels 0) start) (Fin.tail labels) =
        weights 0 start *
          ∏ time : Fin (n + 1),
            weights time.succ
              (finitePathVertex step start labels time.succ)
      congr 1
      rw [ih]
      apply Finset.prod_congr rfl
      intro time _
      rw [finitePathVertex_tail]

noncomputable def uniformProjection {Vertex : Type} [Fintype Vertex] :
    Module.End ℝ (EuclideanSpace ℝ Vertex) where
  toFun := fun value => WithLp.toLp 2 (fun _ =>
    (∑ vertex, value.ofLp vertex) / Fintype.card Vertex)
  map_add' := by
    intro left right
    apply WithLp.ofLp_injective
    funext vertex
    simp [Finset.sum_add_distrib, add_div]
  map_smul' := by
    intro scalar value
    apply WithLp.ofLp_injective
    funext vertex
    change (∑ point, scalar * value.ofLp point) /
        Fintype.card Vertex =
      scalar * ((∑ point, value.ofLp point) / Fintype.card Vertex)
    rw [← Finset.mul_sum]
    ring

noncomputable def indicatorVector {Vertex : Type} [Fintype Vertex]
    (bad : Vertex → Bool) : EuclideanSpace ℝ Vertex :=
  WithLp.toLp 2 fun vertex => bitAsReal (bad vertex)

noncomputable def badProjection {Vertex : Type} [Fintype Vertex]
    (bad : Vertex → Bool) : Module.End ℝ (EuclideanSpace ℝ Vertex) where
  toFun := fun value => WithLp.toLp 2 fun vertex =>
    bitAsReal (bad vertex) * value.ofLp vertex
  map_add' := by
    intro left right
    apply WithLp.ofLp_injective
    funext vertex
    simp [mul_add]
  map_smul' := by
    intro scalar value
    apply WithLp.ofLp_injective
    funext vertex
    change bitAsReal (bad vertex) * (scalar * value.ofLp vertex) =
      scalar * (bitAsReal (bad vertex) * value.ofLp vertex)
    ring

theorem indicatorVector_norm_sq {Vertex : Type} [Fintype Vertex]
    (bad : Vertex → Bool) :
    ‖indicatorVector bad‖ ^ 2 = ∑ vertex, bitAsReal (bad vertex) := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro vertex _
  cases hbad : bad vertex <;> simp [indicatorVector, bitAsReal, hbad]

theorem badProjection_norm_le {Vertex : Type} [Fintype Vertex]
    (bad : Vertex → Bool) (value : EuclideanSpace ℝ Vertex) :
    ‖badProjection bad value‖ ≤ ‖value‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro vertex _
  cases hbad : bad vertex
  · have hsquare := sq_nonneg (value.ofLp vertex)
    simpa [badProjection, bitAsReal, hbad] using hsquare
  · simp [badProjection, bitAsReal, hbad]

theorem bad_uniform_bad_norm_le
    {Vertex : Type} [Fintype Vertex] [Nonempty Vertex]
    (bad : Vertex → Bool) (value : EuclideanSpace ℝ Vertex) :
    ‖badProjection bad (uniformProjection (badProjection bad value))‖ ≤
      booleanMean bad * ‖value‖ := by
  have hcardNat : 0 < Fintype.card Vertex := Fintype.card_pos
  have hcard : (0 : ℝ) < Fintype.card Vertex := by
    exact_mod_cast hcardNat
  have hinner := abs_real_inner_le_norm (indicatorVector bad) value
  change ‖WithLp.toLp 2 (fun vertex =>
      bitAsReal (bad vertex) *
        ((∑ point, bitAsReal (bad point) * value.ofLp point) /
          Fintype.card Vertex))‖ ≤ _
  have hrewrite :
      (∑ point, bitAsReal (bad point) * value.ofLp point) =
        @inner ℝ _ _ (indicatorVector bad) value := by
    change (∑ point, bitAsReal (bad point) * value.ofLp point) =
      ∑ point, value.ofLp point * bitAsReal (bad point)
    apply Finset.sum_congr rfl
    intro point _
    ring
  rw [hrewrite]
  have hvector : WithLp.toLp 2 (fun vertex =>
      bitAsReal (bad vertex) *
        ((@inner ℝ _ _ (indicatorVector bad) value) /
          Fintype.card Vertex)) =
      ((@inner ℝ _ _ (indicatorVector bad) value) /
        Fintype.card Vertex) • indicatorVector bad := by
    apply WithLp.ofLp_injective
    funext vertex
    change bitAsReal (bad vertex) *
        ((@inner ℝ _ _ (indicatorVector bad) value) /
          Fintype.card Vertex) =
      ((@inner ℝ _ _ (indicatorVector bad) value) /
        Fintype.card Vertex) * bitAsReal (bad vertex)
    ring
  rw [hvector, norm_smul, Real.norm_eq_abs]
  rw [abs_div, abs_of_pos hcard]
  unfold booleanMean
  rw [← indicatorVector_norm_sq]
  calc
    |@inner ℝ _ _ (indicatorVector bad) value| /
          (Fintype.card Vertex : ℝ) * ‖indicatorVector bad‖ ≤
        (‖indicatorVector bad‖ * ‖value‖) /
          (Fintype.card Vertex : ℝ) * ‖indicatorVector bad‖ := by
      gcongr
    _ = ‖indicatorVector bad‖ ^ 2 /
          (Fintype.card Vertex : ℝ) * ‖value‖ := by ring

/-! ## Concrete fortieth-power walk and majority experiment -/

def duplicatedMargulisLabel (label : Fin 16) : Fin 8 :=
  ⟨label.val % 8, Nat.mod_lt _ (by omega)⟩

def duplicatedMargulisNeighbor {m : ℕ} [NeZero m]
    (label : Fin 16) (vertex : MargulisVertex m) : MargulisVertex m :=
  margulisNeighbor (duplicatedMargulisLabel label) vertex

noncomputable def normalizedMargulisFull {m : ℕ} [NeZero m] :
    Module.End ℝ (EuclideanSpace ℝ (MargulisVertex m)) where
  toFun := fun value => WithLp.toLp 2 (fun vertex =>
    margulisAdjacency value.ofLp vertex / 8)
  map_add' := by
    intro left right
    apply WithLp.ofLp_injective
    funext vertex
    simp [margulisAdjacency, Finset.sum_add_distrib, add_div]
  map_smul' := by
    intro scalar value
    apply WithLp.ofLp_injective
    funext vertex
    change (∑ label : Fin 8,
        scalar * value.ofLp (margulisNeighbor label vertex)) / 8 =
      scalar * ((∑ label : Fin 8,
        value.ofLp (margulisNeighbor label vertex)) / 8)
    rw [← Finset.mul_sum]
    ring

theorem sum_duplicatedMargulisLabel (f : Fin 8 → ℝ) :
    (∑ label : Fin 16, f (duplicatedMargulisLabel label)) =
      2 * ∑ label : Fin 8, f label := by
  simp [Fin.sum_univ_succ, duplicatedMargulisLabel]
  ring

theorem averageStep_duplicatedMargulis
    {m : ℕ} [NeZero m] :
    averageStep (duplicatedMargulisNeighbor (m := m)) =
      normalizedMargulisFull := by
  ext value vertex
  change (∑ label : Fin 16,
      value.ofLp (margulisNeighbor (duplicatedMargulisLabel label) vertex)) /
        16 = margulisAdjacency value.ofLp vertex / 8
  rw [show (∑ label : Fin 16,
      value.ofLp (margulisNeighbor (duplicatedMargulisLabel label) vertex)) =
        2 * ∑ label : Fin 8,
          value.ofLp (margulisNeighbor label vertex) from
    sum_duplicatedMargulisLabel
      (fun label => value.ofLp (margulisNeighbor label vertex))]
  simp only [margulisAdjacency]
  ring

abbrev PoweredMargulisLabel := Fin 40 → Fin 16

def poweredMargulisNeighbor {m : ℕ} [NeZero m]
    (label : PoweredMargulisLabel)
    (vertex : MargulisVertex m) : MargulisVertex m :=
  tupleWalk duplicatedMargulisNeighbor label vertex

set_option maxRecDepth 20000 in
theorem uniform_poweredMargulisNeighbor_eq_operator
    {m : ℕ} [NeZero m]
    (value : EuclideanSpace ℝ (MargulisVertex m))
    (vertex : MargulisVertex m) :
    (∑ label : PoweredMargulisLabel,
      value.ofLp (poweredMargulisNeighbor label vertex)) /
        (16 : ℝ) ^ 40 =
      ((normalizedMargulisFull ^ 40) value).ofLp vertex := by
  change (∑ label : Fin 40 → Fin 16,
      value.ofLp (tupleWalk duplicatedMargulisNeighbor label vertex)) /
        (16 : ℝ) ^ 40 =
      ((normalizedMargulisFull ^ 40) value).ofLp vertex
  rw [sum_tupleWalk duplicatedMargulisNeighbor (by norm_num)]
  rw [averageStep_duplicatedMargulis]
  norm_num

theorem card_poweredMargulisLabel :
    Fintype.card PoweredMargulisLabel = 16 ^ 40 := by
  simp [PoweredMargulisLabel]

theorem sum_poweredMargulisNeighbor
    {m : ℕ} [NeZero m]
    (value : EuclideanSpace ℝ (MargulisVertex m))
    (vertex : MargulisVertex m) :
    (∑ label : PoweredMargulisLabel,
      value.ofLp (poweredMargulisNeighbor label vertex)) =
      Fintype.card PoweredMargulisLabel *
        ((normalizedMargulisFull ^ 40) value).ofLp vertex := by
  have h :=
    uniform_poweredMargulisNeighbor_eq_operator value vertex
  have hnonzero : (16 : ℝ) ^ 40 ≠ 0 := by positivity
  rw [div_eq_iff hnonzero] at h
  rw [card_poweredMargulisLabel]
  norm_num at h ⊢
  linarith

noncomputable def centeredMargulisValue {m : ℕ} [NeZero m]
    (value : EuclideanSpace ℝ (MargulisVertex m)) :
    meanZeroSubmodule (m := m) :=
  ⟨value - uniformProjection value, by
    change ∑ vertex, (value.ofLp vertex -
      (∑ point, value.ofLp point) /
        Fintype.card (MargulisVertex m)) = 0
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card (MargulisVertex m) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt Fintype.card_pos)
    field_simp
    ring⟩

theorem centeredMargulisValue_add_uniform {m : ℕ} [NeZero m]
    (value : EuclideanSpace ℝ (MargulisVertex m)) :
    (centeredMargulisValue value).val + uniformProjection value = value := by
  simp [centeredMargulisValue]

theorem centeredMargulisValue_inner_uniform_eq_zero
    {m : ℕ} [NeZero m]
    (value : EuclideanSpace ℝ (MargulisVertex m)) :
    @inner ℝ _ _ (centeredMargulisValue value).val
      (uniformProjection value) = 0 := by
  change ∑ vertex,
      ((∑ point, value.ofLp point) /
        Fintype.card (MargulisVertex m)) *
        (value.ofLp vertex -
          (∑ point, value.ofLp point) /
            Fintype.card (MargulisVertex m)) = 0
  rw [← Finset.mul_sum]
  change ((∑ point, value.ofLp point) /
      Fintype.card (MargulisVertex m)) *
    (∑ vertex, (centeredMargulisValue value).val.ofLp vertex) = 0
  have hzero :
      ∑ vertex, (centeredMargulisValue value).val.ofLp vertex = 0 := by
    exact (centeredMargulisValue value).property
  rw [hzero]
  ring

theorem centeredMargulisValue_norm_le
    {m : ℕ} [NeZero m]
    (value : EuclideanSpace ℝ (MargulisVertex m)) :
    ‖(centeredMargulisValue value).val‖ ≤ ‖value‖ := by
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (centeredMargulisValue value).val (uniformProjection value)
    (centeredMargulisValue_inner_uniform_eq_zero value)
  rw [centeredMargulisValue_add_uniform] at hpyth
  nlinarith [norm_nonneg ((centeredMargulisValue value).val),
    norm_nonneg value, sq_nonneg ‖uniformProjection value‖]

theorem normalizedMargulisFull_on_meanZero
    {m : ℕ} [NeZero m]
    (value : meanZeroSubmodule (m := m)) :
    normalizedMargulisFull value.val =
      (normalizedMargulisMeanZero value).val := by
  apply WithLp.ofLp_injective
  funext vertex
  change margulisAdjacency value.val.ofLp vertex / 8 =
    (1 / 8 : ℝ) * margulisAdjacency value.val.ofLp vertex
  ring

theorem normalizedMargulisFull_power_on_meanZero
    {m : ℕ} [NeZero m]
    (iterations : ℕ) (value : meanZeroSubmodule (m := m)) :
    (normalizedMargulisFull ^ iterations) value.val =
      ((normalizedMargulisMeanZero ^ iterations) value).val := by
  induction iterations with
  | zero => simp
  | succ iterations ih =>
      rw [pow_succ', pow_succ']
      change normalizedMargulisFull
          ((normalizedMargulisFull ^ iterations) value.val) =
        (normalizedMargulisMeanZero
          ((normalizedMargulisMeanZero ^ iterations) value)).val
      rw [ih]
      exact normalizedMargulisFull_on_meanZero _

theorem normalizedMargulisFull_uniform
    {m : ℕ} [NeZero m]
    (value : EuclideanSpace ℝ (MargulisVertex m)) :
    normalizedMargulisFull (uniformProjection value) =
      uniformProjection value := by
  apply WithLp.ofLp_injective
  funext vertex
  change margulisAdjacency (fun _ =>
      (∑ point, value.ofLp point) /
        Fintype.card (MargulisVertex m)) vertex / 8 =
    (∑ point, value.ofLp point) / Fintype.card (MargulisVertex m)
  rw [constant_margulisEigenvector]
  ring

theorem normalizedMargulisFull_power_uniform
    {m : ℕ} [NeZero m]
    (iterations : ℕ)
    (value : EuclideanSpace ℝ (MargulisVertex m)) :
    (normalizedMargulisFull ^ iterations) (uniformProjection value) =
      uniformProjection value := by
  induction iterations with
  | zero => simp
  | succ iterations ih =>
      rw [pow_succ']
      change normalizedMargulisFull
          ((normalizedMargulisFull ^ iterations)
            (uniformProjection value)) = _
      rw [ih]
      exact normalizedMargulisFull_uniform value

theorem normalizedMargulisFull_residual_eq_meanZero
    {m : ℕ} [NeZero m]
    (iterations : ℕ)
    (value : EuclideanSpace ℝ (MargulisVertex m)) :
    (normalizedMargulisFull ^ iterations) value - uniformProjection value =
      ((normalizedMargulisMeanZero ^ iterations)
        (centeredMargulisValue value)).val := by
  have hdecomp := centeredMargulisValue_add_uniform value
  conv_lhs =>
    lhs
    rw [← hdecomp]
  rw [map_add, normalizedMargulisFull_power_uniform]
  rw [add_sub_cancel_right]
  exact normalizedMargulisFull_power_on_meanZero iterations _

set_option maxHeartbeats 800000 in
-- Elaborating the generic finite-dimensional power bound exceeds the default.
set_option maxRecDepth 20000 in
theorem normalizedMargulisFull_residual_norm_bound
    (spectrum : ExpanderSpectrumContract)
    {m : ℕ} [NeZero m]
    (iterations : ℕ)
    (value : EuclideanSpace ℝ (MargulisVertex m)) :
    ‖(normalizedMargulisFull ^ iterations) value -
        uniformProjection value‖ ≤
      (5 * Real.sqrt 2 / 8) ^ iterations * ‖value‖ := by
  rw [normalizedMargulisFull_residual_eq_meanZero]
  calc
    ‖((normalizedMargulisMeanZero ^ iterations)
        (centeredMargulisValue value)).val‖ =
        ‖(normalizedMargulisMeanZero ^ iterations)
          (centeredMargulisValue value)‖ := rfl
    _ ≤ (5 * Real.sqrt 2 / 8) ^ iterations *
          ‖centeredMargulisValue value‖ := by
      exact iterated_norm_le
        (E := meanZeroSubmodule (m := m))
        normalizedMargulisMeanZero
        (5 * Real.sqrt 2 / 8) (by positivity)
        (normalizedMargulisMeanZero_norm_bound spectrum)
        iterations _
    _ ≤ (5 * Real.sqrt 2 / 8) ^ iterations * ‖value‖ := by
      apply mul_le_mul_of_nonneg_left
        (centeredMargulisValue_norm_le value)
      positivity

theorem poweredMargulis_residual_eq_meanZero
    {m : ℕ} [NeZero m]
    (value : EuclideanSpace ℝ (MargulisVertex m)) :
    (normalizedMargulisFull ^ 40) value - uniformProjection value =
      ((normalizedMargulisMeanZero ^ 40)
        (centeredMargulisValue value)).val := by
  exact normalizedMargulisFull_residual_eq_meanZero 40 value

theorem poweredMargulis_residual_norm_bound
    (spectrum : ExpanderSpectrumContract)
    {m : ℕ} [NeZero m]
    (value : EuclideanSpace ℝ (MargulisVertex m)) :
    ‖(normalizedMargulisFull ^ 40) value - uniformProjection value‖ ≤
      (5 * Real.sqrt 2 / 8) ^ 40 * ‖value‖ := by
  exact normalizedMargulisFull_residual_norm_bound spectrum 40 value

theorem normalizedMargulis_bad_sandwich_norm_bound
    (spectrum : ExpanderSpectrumContract)
    {m : ℕ} [NeZero m]
    (iterations : ℕ)
    (bad : MargulisVertex m → Bool)
    (value : EuclideanSpace ℝ (MargulisVertex m)) :
    ‖badProjection bad
        ((normalizedMargulisFull ^ iterations)
          (badProjection bad value))‖ ≤
      (booleanMean bad + (5 * Real.sqrt 2 / 8) ^ iterations) *
        ‖value‖ := by
  let projected := badProjection bad value
  let residual :=
    (normalizedMargulisFull ^ iterations) projected -
      uniformProjection projected
  have hdecomp :
      (normalizedMargulisFull ^ iterations) projected =
        uniformProjection projected + residual := by
    simp [residual]
  rw [show badProjection bad
      ((normalizedMargulisFull ^ iterations)
        (badProjection bad value)) =
      badProjection bad
        ((normalizedMargulisFull ^ iterations) projected) by rfl]
  rw [hdecomp, map_add]
  calc
    ‖badProjection bad (uniformProjection projected) +
        badProjection bad residual‖ ≤
      ‖badProjection bad (uniformProjection projected)‖ +
        ‖badProjection bad residual‖ := norm_add_le _ _
    _ ≤ booleanMean bad * ‖value‖ +
        (5 * Real.sqrt 2 / 8) ^ iterations * ‖value‖ := by
      apply add_le_add
      · exact bad_uniform_bad_norm_le bad value
      · calc
          ‖badProjection bad residual‖ ≤ ‖residual‖ :=
            badProjection_norm_le bad residual
          _ ≤ (5 * Real.sqrt 2 / 8) ^ iterations * ‖projected‖ :=
            normalizedMargulisFull_residual_norm_bound
              spectrum iterations projected
          _ ≤ (5 * Real.sqrt 2 / 8) ^ iterations * ‖value‖ := by
            apply mul_le_mul_of_nonneg_left
              (badProjection_norm_le bad value)
            positivity
    _ = (booleanMean bad + (5 * Real.sqrt 2 / 8) ^ iterations) *
          ‖value‖ := by ring

/-- The exact projection-operator estimate used by the multiple-hit argument.
Both appearances of the bad-set projector are essential: the uniform part has
operator norm exactly its density, while the residual part costs the powered
spectral radius. -/
theorem poweredMargulis_bad_sandwich_norm_bound
    (spectrum : ExpanderSpectrumContract)
    {m : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool)
    (value : EuclideanSpace ℝ (MargulisVertex m)) :
    ‖badProjection bad
        ((normalizedMargulisFull ^ 40) (badProjection bad value))‖ ≤
      (booleanMean bad + (5 * Real.sqrt 2 / 8) ^ 40) * ‖value‖ := by
  exact normalizedMargulis_bad_sandwich_norm_bound
    spectrum 40 bad value

theorem baseMargulisRadius_le_one :
    5 * Real.sqrt 2 / 8 ≤ (1 : ℝ) := by
  have hsquare : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by norm_num
  have hsqrt : Real.sqrt 2 < (8 : ℝ) / 5 := by
    nlinarith [Real.sqrt_nonneg 2]
  linarith

theorem poweredMargulis_gap_bad_sandwich_norm_bound
    (spectrum : ExpanderSpectrumContract)
    {m : ℕ} [NeZero m]
    (gap : ℕ) (hgap : 0 < gap)
    (bad : MargulisVertex m → Bool)
    (value : EuclideanSpace ℝ (MargulisVertex m)) :
    ‖badProjection bad
        (((normalizedMargulisFull ^ 40) ^ gap)
          (badProjection bad value))‖ ≤
      (booleanMean bad + (5 * Real.sqrt 2 / 8) ^ 40) *
        ‖value‖ := by
  rw [← pow_mul]
  calc
    ‖badProjection bad
        ((normalizedMargulisFull ^ (40 * gap))
          (badProjection bad value))‖ ≤
      (booleanMean bad + (5 * Real.sqrt 2 / 8) ^ (40 * gap)) *
        ‖value‖ :=
      normalizedMargulis_bad_sandwich_norm_bound
        spectrum (40 * gap) bad value
    _ ≤ (booleanMean bad + (5 * Real.sqrt 2 / 8) ^ 40) *
        ‖value‖ := by
      apply mul_le_mul_of_nonneg_right
      · apply add_le_add le_rfl
        apply pow_le_pow_of_le_one (by positivity)
          baseMargulisRadius_le_one
        omega
      · exact norm_nonneg _

theorem sum_badProjection_eq_inner
    {Vertex : Type} [Fintype Vertex]
    (bad : Vertex → Bool) (value : EuclideanSpace ℝ Vertex) :
    (∑ vertex, (badProjection bad value).ofLp vertex) =
      @inner ℝ _ _ (indicatorVector bad) value := by
  change (∑ vertex, bitAsReal (bad vertex) * value.ofLp vertex) =
    ∑ vertex, value.ofLp vertex * bitAsReal (bad vertex)
  apply Finset.sum_congr rfl
  intro vertex _
  ring

theorem badProjection_idempotent
    {Vertex : Type} [Fintype Vertex]
    (bad : Vertex → Bool) (value : EuclideanSpace ℝ Vertex) :
    badProjection bad (badProjection bad value) =
      badProjection bad value := by
  apply WithLp.ofLp_injective
  funext vertex
  cases hbad : bad vertex <;>
    simp [badProjection, bitAsReal, hbad]

theorem badProjection_indicator
    {Vertex : Type} [Fintype Vertex]
    (bad : Vertex → Bool) :
    badProjection bad (indicatorVector bad) = indicatorVector bad := by
  apply WithLp.ofLp_injective
  funext vertex
  cases hbad : bad vertex <;>
    simp [badProjection, indicatorVector, bitAsReal, hbad]

/-- `gaps` lists the positive distances between consecutive selected times.
The recursion is the exact projected transition product, starting from the
last selected time. -/
noncomputable def jointHitVector
    {m : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool) :
    List ℕ → EuclideanSpace ℝ (MargulisVertex m)
  | [] => indicatorVector bad
  | gap :: gaps =>
      badProjection bad
        (((normalizedMargulisFull ^ 40) ^ gap)
          (jointHitVector bad gaps))

theorem jointHitVector_supported
    {m : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool) (gaps : List ℕ) :
    badProjection bad (jointHitVector bad gaps) =
      jointHitVector bad gaps := by
  cases gaps with
  | nil => exact badProjection_indicator bad
  | cons gap gaps => exact badProjection_idempotent bad _

theorem jointHitVector_norm_bound
    (spectrum : ExpanderSpectrumContract)
    {m : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool) (gaps : List ℕ)
    (hpositive : ∀ gap ∈ gaps, 0 < gap) :
    ‖jointHitVector bad gaps‖ ≤
      (booleanMean bad + (5 * Real.sqrt 2 / 8) ^ 40) ^ gaps.length *
        ‖indicatorVector bad‖ := by
  induction gaps with
  | nil => simp [jointHitVector]
  | cons gap gaps ih =>
      have hgap : 0 < gap := hpositive gap (by simp)
      have htail : ∀ candidate ∈ gaps, 0 < candidate := by
        intro candidate hcandidate
        exact hpositive candidate (by simp [hcandidate])
      have ih' := ih htail
      have hsupported := jointHitVector_supported bad gaps
      change ‖badProjection bad
          (((normalizedMargulisFull ^ 40) ^ gap)
            (jointHitVector bad gaps))‖ ≤ _
      rw [← hsupported]
      calc
        ‖badProjection bad
            (((normalizedMargulisFull ^ 40) ^ gap)
              (badProjection bad (jointHitVector bad gaps)))‖ ≤
          (booleanMean bad + (5 * Real.sqrt 2 / 8) ^ 40) *
            ‖jointHitVector bad gaps‖ :=
          poweredMargulis_gap_bad_sandwich_norm_bound
            spectrum gap hgap bad _
        _ ≤ (booleanMean bad + (5 * Real.sqrt 2 / 8) ^ 40) *
            ((booleanMean bad + (5 * Real.sqrt 2 / 8) ^ 40) ^
              gaps.length * ‖indicatorVector bad‖) := by
          apply mul_le_mul_of_nonneg_left ih'
          apply add_nonneg
          · unfold booleanMean
            apply div_nonneg
            · apply Finset.sum_nonneg
              intro vertex _
              cases bad vertex <;> simp [bitAsReal]
            · positivity
          · positivity
        _ = (booleanMean bad + (5 * Real.sqrt 2 / 8) ^ 40) ^
              (gap :: gaps).length * ‖indicatorVector bad‖ := by
          simp only [List.length_cons, pow_succ']
          ring

noncomputable def jointHitOperatorProbability
    {m : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool) (gaps : List ℕ) : ℝ :=
  (∑ vertex, (jointHitVector bad gaps).ofLp vertex) /
    Fintype.card (MargulisVertex m)

/-- The manuscript's projection-operator multiple-hit inequality, now derived
from the concrete Margulis adjacency and its exact powered transition. -/
theorem jointHitOperatorProbability_le
    (spectrum : ExpanderSpectrumContract)
    {m : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool) (gaps : List ℕ)
    (hpositive : ∀ gap ∈ gaps, 0 < gap) :
    jointHitOperatorProbability bad gaps ≤
      booleanMean bad *
        (booleanMean bad + (5 * Real.sqrt 2 / 8) ^ 40) ^ gaps.length := by
  have hcardNat : 0 < Fintype.card (MargulisVertex m) :=
    Fintype.card_pos
  have hcard : (0 : ℝ) < Fintype.card (MargulisVertex m) := by
    exact_mod_cast hcardNat
  have hsupported := jointHitVector_supported bad gaps
  have hsum :
      (∑ vertex, (jointHitVector bad gaps).ofLp vertex) =
        @inner ℝ _ _ (indicatorVector bad)
          (jointHitVector bad gaps) := by
    calc
      (∑ vertex, (jointHitVector bad gaps).ofLp vertex) =
          ∑ vertex,
            (badProjection bad (jointHitVector bad gaps)).ofLp vertex := by
        rw [hsupported]
      _ = @inner ℝ _ _ (indicatorVector bad)
          (jointHitVector bad gaps) :=
        sum_badProjection_eq_inner bad _
  have hdensity : booleanMean bad =
      ‖indicatorVector bad‖ ^ 2 /
        Fintype.card (MargulisVertex m) := by
    unfold booleanMean
    rw [indicatorVector_norm_sq]
  unfold jointHitOperatorProbability
  rw [hsum]
  have hinner := abs_real_inner_le_norm
    (indicatorVector bad) (jointHitVector bad gaps)
  have hjoint :=
    jointHitVector_norm_bound spectrum bad gaps hpositive
  calc
    (@inner ℝ _ _ (indicatorVector bad) (jointHitVector bad gaps)) /
        (Fintype.card (MargulisVertex m) : ℝ) ≤
      |@inner ℝ _ _ (indicatorVector bad)
        (jointHitVector bad gaps)| /
        (Fintype.card (MargulisVertex m) : ℝ) := by
      apply div_le_div_of_nonneg_right (le_abs_self _) hcard.le
    _ ≤ (‖indicatorVector bad‖ * ‖jointHitVector bad gaps‖) /
        (Fintype.card (MargulisVertex m) : ℝ) := by
      apply div_le_div_of_nonneg_right hinner hcard.le
    _ ≤ (‖indicatorVector bad‖ *
          ((booleanMean bad + (5 * Real.sqrt 2 / 8) ^ 40) ^
            gaps.length * ‖indicatorVector bad‖)) /
        (Fintype.card (MargulisVertex m) : ℝ) := by
      apply div_le_div_of_nonneg_right _ hcard.le
      apply mul_le_mul_of_nonneg_left hjoint (norm_nonneg _)
    _ = ‖indicatorVector bad‖ ^ 2 /
          (Fintype.card (MargulisVertex m) : ℝ) *
        (booleanMean bad + (5 * Real.sqrt 2 / 8) ^ 40) ^
          gaps.length := by
      ring
    _ = booleanMean bad *
        (booleanMean bad + (5 * Real.sqrt 2 / 8) ^ 40) ^
          gaps.length := by
      rw [hdensity]

structure MargulisWalkSample (m t : ℕ) [NeZero m] where
  start : MargulisVertex m
  transitions : Fin (t - 1) → PoweredMargulisLabel
  deriving Fintype

def MargulisWalkSample.vertex {m t : ℕ} [NeZero m]
    (sample : MargulisWalkSample m t) :
    Fin t → MargulisVertex m
  | ⟨0, _⟩ => sample.start
  | ⟨time + 1, htime⟩ =>
      poweredMargulisNeighbor
        (sample.transitions ⟨time, by omega⟩)
        (sample.vertex ⟨time, by omega⟩)
termination_by time => time.val

def sampleTransitionLabels
    {m n : ℕ} [NeZero m]
    (sample : MargulisWalkSample m n.succ) :
    Fin n → PoweredMargulisLabel :=
  fun time => sample.transitions ⟨time.val, by omega⟩

theorem sample_vertex_nat_eq_finitePathVertex
    {m n : ℕ} [NeZero m]
    (sample : MargulisWalkSample m n.succ)
    (time : ℕ) (htime : time < n.succ) :
    sample.vertex ⟨time, htime⟩ =
      finitePathVertex poweredMargulisNeighbor sample.start
        (sampleTransitionLabels sample) ⟨time, htime⟩ := by
  induction time using Nat.strong_induction_on with
  | h time ih =>
      cases time with
      | zero =>
          rw [MargulisWalkSample.vertex.eq_def]
          change sample.start =
            finitePathVertex poweredMargulisNeighbor sample.start
              (sampleTransitionLabels sample) 0
          rw [finitePathVertex_zero]
      | succ previous =>
          rw [MargulisWalkSample.vertex.eq_def]
          change poweredMargulisNeighbor
              (sampleTransitionLabels sample ⟨previous, by omega⟩)
              (sample.vertex ⟨previous, by omega⟩) =
            finitePathVertex poweredMargulisNeighbor sample.start
              (sampleTransitionLabels sample) ⟨previous + 1, htime⟩
          let previousFin : Fin n := ⟨previous, by omega⟩
          have ihPrevious := ih previous (by omega) (by omega)
          calc
            poweredMargulisNeighbor
                (sampleTransitionLabels sample previousFin)
                (sample.vertex ⟨previous, by omega⟩) =
              poweredMargulisNeighbor
                (sampleTransitionLabels sample previousFin)
                (finitePathVertex poweredMargulisNeighbor sample.start
                  (sampleTransitionLabels sample)
                    previousFin.castSucc) :=
              congrArg
                (poweredMargulisNeighbor
                  (sampleTransitionLabels sample previousFin))
                ihPrevious
            _ = finitePathVertex poweredMargulisNeighbor sample.start
                (sampleTransitionLabels sample) previousFin.succ := by
              symm
              exact finitePathVertex_succ poweredMargulisNeighbor
                sample.start (sampleTransitionLabels sample) previousFin
            _ = finitePathVertex poweredMargulisNeighbor sample.start
                (sampleTransitionLabels sample)
                  ⟨previous + 1, htime⟩ := by
              congr

theorem sample_vertex_eq_finitePathVertex
    {m n : ℕ} [NeZero m]
    (sample : MargulisWalkSample m n.succ)
    (time : Fin n.succ) :
    sample.vertex time =
      finitePathVertex poweredMargulisNeighbor sample.start
        (sampleTransitionLabels sample) time := by
  exact sample_vertex_nat_eq_finitePathVertex
    sample time.val time.isLt

def concreteBadAt {m t : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool)
    (sample : MargulisWalkSample m t) (time : Fin t) : Bool :=
  bad (sample.vertex time)

def selectedVertexWeight {m n : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool)
    (times : Finset (Fin n.succ))
    (time : Fin n.succ) (vertex : MargulisVertex m) : ℝ :=
  if time ∈ times then bitAsReal (bad vertex) else 1

theorem bitAsReal_selectedCondition_eq_product
    {m n : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool)
    (times : Finset (Fin n.succ))
    (sample : MargulisWalkSample m n.succ) :
    bitAsReal (decide (∀ time ∈ times,
      concreteBadAt bad sample time = true)) =
      ∏ time : Fin n.succ,
        selectedVertexWeight bad times time (sample.vertex time) := by
  classical
  by_cases hall :
      ∀ time ∈ times, concreteBadAt bad sample time = true
  · rw [decide_eq_true hall]
    simp only [bitAsReal, if_true]
    symm
    apply Finset.prod_eq_one
    intro time _
    by_cases htime : time ∈ times
    · rw [selectedVertexWeight, if_pos htime]
      have hbad : bad (sample.vertex time) = true := hall time htime
      rw [hbad]
      rfl
    · simp [selectedVertexWeight, htime]
  · have hdecide :
        decide (∀ time ∈ times,
          concreteBadAt bad sample time = true) = false := by
      exact decide_eq_false hall
    rw [hdecide]
    simp only [bitAsReal, Bool.false_eq_true, if_false]
    push Not at hall
    obtain ⟨time, htime, hbad⟩ := hall
    have hbadFalse : bad (sample.vertex time) = false := by
      simpa [concreteBadAt] using hbad
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ time)
    simp [selectedVertexWeight, htime, hbadFalse, bitAsReal]

theorem selectedCondition_pathWeight
    {m n : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool)
    (times : Finset (Fin n.succ))
    (sample : MargulisWalkSample m n.succ) :
    bitAsReal (decide (∀ time ∈ times,
      concreteBadAt bad sample time = true)) =
      finitePathWeight poweredMargulisNeighbor
        (selectedVertexWeight bad times)
        sample.start (sampleTransitionLabels sample) := by
  rw [finitePathWeight_eq_product]
  calc
    bitAsReal (decide (∀ time ∈ times,
        concreteBadAt bad sample time = true)) =
      ∏ time : Fin n.succ,
        selectedVertexWeight bad times time (sample.vertex time) :=
      bitAsReal_selectedCondition_eq_product bad times sample
    _ = ∏ time : Fin n.succ,
        selectedVertexWeight bad times time
          (finitePathVertex poweredMargulisNeighbor sample.start
            (sampleTransitionLabels sample) time) := by
      apply Finset.prod_congr rfl
      intro time _
      rw [sample_vertex_eq_finitePathVertex]

def positiveSampleEquiv {m n : ℕ} [NeZero m] :
    MargulisWalkSample m n.succ ≃
      MargulisVertex m × (Fin n → PoweredMargulisLabel) where
  toFun sample := (sample.start, sampleTransitionLabels sample)
  invFun pair :=
    { start := pair.1
      transitions := fun time => pair.2 ⟨time.val, by omega⟩ }
  left_inv sample := by
    cases sample
    congr
  right_inv pair := by
    rcases pair with ⟨start, labels⟩
    apply Prod.ext
    · rfl
    · funext time
      rfl

@[simp] theorem positiveSampleEquiv_start
    {m n : ℕ} [NeZero m]
    (pair : MargulisVertex m × (Fin n → PoweredMargulisLabel)) :
    (positiveSampleEquiv.symm pair).start = pair.1 := rfl

@[simp] theorem positiveSampleEquiv_labels
    {m n : ℕ} [NeZero m]
    (pair : MargulisVertex m × (Fin n → PoweredMargulisLabel)) :
    sampleTransitionLabels (positiveSampleEquiv.symm pair) = pair.2 := by
  funext time
  rfl

noncomputable def selectedPathValue {m n : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool)
    (times : Finset (Fin n.succ)) :
    EuclideanSpace ℝ (MargulisVertex m) :=
  finitePathValue (normalizedMargulisFull ^ 40)
    (selectedVertexWeight bad times)

theorem sum_selectedCondition
    {m n : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool)
    (times : Finset (Fin n.succ)) :
    (∑ sample : MargulisWalkSample m n.succ,
      bitAsReal (decide (∀ time ∈ times,
        concreteBadAt bad sample time = true))) =
      (Fintype.card PoweredMargulisLabel : ℝ) ^ n *
        ∑ vertex, (selectedPathValue bad times).ofLp vertex := by
  rw [← Equiv.sum_comp positiveSampleEquiv.symm
    (fun sample : MargulisWalkSample m n.succ =>
      bitAsReal (decide (∀ time ∈ times,
        concreteBadAt bad sample time = true)))]
  rw [Fintype.sum_prod_type]
  change (∑ start : MargulisVertex m,
    ∑ labels : Fin n → PoweredMargulisLabel,
      bitAsReal (decide (∀ time ∈ times,
        concreteBadAt bad
          (positiveSampleEquiv.symm (start, labels)) time = true))) = _
  simp_rw [selectedCondition_pathWeight]
  simp only [positiveSampleEquiv_start, positiveSampleEquiv_labels]
  simp_rw [sum_finitePathWeight poweredMargulisNeighbor
    (normalizedMargulisFull ^ 40) sum_poweredMargulisNeighbor]
  unfold selectedPathValue
  rw [Finset.mul_sum]

theorem card_positiveSample
    {m n : ℕ} [NeZero m] :
    Fintype.card (MargulisWalkSample m n.succ) =
      Fintype.card (MargulisVertex m) *
        Fintype.card PoweredMargulisLabel ^ n := by
  rw [Fintype.card_congr (positiveSampleEquiv (m := m) (n := n))]
  simp

theorem booleanMean_selectedCondition_eq_pathValue
    {m n : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool)
    (times : Finset (Fin n.succ)) :
    booleanMean (fun sample : MargulisWalkSample m n.succ =>
      decide (∀ time ∈ times,
        concreteBadAt bad sample time = true)) =
      (∑ vertex, (selectedPathValue bad times).ofLp vertex) /
        Fintype.card (MargulisVertex m) := by
  unfold booleanMean
  rw [sum_selectedCondition, card_positiveSample]
  have hlabels : (0 : ℝ) <
      (Fintype.card PoweredMargulisLabel : ℝ) ^ n := by
    positivity
  have hvertices :
      (0 : ℝ) < Fintype.card (MargulisVertex m) := by
    exact_mod_cast Fintype.card_pos
  push_cast
  field_simp

def tailSelectedTimes {n : ℕ}
    (times : Finset (Fin (n + 2))) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun time => time.succ ∈ times

@[simp] theorem mem_tailSelectedTimes {n : ℕ}
    (times : Finset (Fin (n + 2))) (time : Fin (n + 1)) :
    time ∈ tailSelectedTimes times ↔ time.succ ∈ times := by
  simp [tailSelectedTimes]

theorem map_tailSelectedTimes {n : ℕ}
    (times : Finset (Fin (n + 2))) :
    (tailSelectedTimes times).map (Fin.succEmb (n + 1)) =
      times.erase 0 := by
  ext time
  refine Fin.cases ?_ (fun previous => ?_) time
  · simp
  · simp [tailSelectedTimes]

theorem card_tailSelectedTimes {n : ℕ}
    (times : Finset (Fin (n + 2))) :
    (tailSelectedTimes times).card =
      if 0 ∈ times then times.card - 1 else times.card := by
  have hcard := congrArg Finset.card (map_tailSelectedTimes times)
  simp only [Finset.card_map] at hcard
  rw [hcard]
  by_cases hzero : 0 ∈ times
  · rw [Finset.card_erase_of_mem hzero, if_pos hzero]
  · rw [Finset.erase_eq_of_notMem hzero, if_neg hzero]

theorem selectedVertexWeight_tail
    {m n : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool)
    (times : Finset (Fin (n + 2))) :
    (fun time => selectedVertexWeight bad times time.succ) =
      selectedVertexWeight bad (tailSelectedTimes times) := by
  funext time vertex
  simp [selectedVertexWeight, tailSelectedTimes]

set_option maxHeartbeats 800000 in
-- The dependent finite-path recursion needs additional elaboration budget.
theorem selectedPathValue_succ
    {m n : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool)
    (times : Finset (Fin (n + 2))) :
    selectedPathValue bad times =
      if 0 ∈ times then
        badProjection bad
          ((normalizedMargulisFull ^ 40)
            (selectedPathValue bad (tailSelectedTimes times)))
      else
        (normalizedMargulisFull ^ 40)
          (selectedPathValue bad (tailSelectedTimes times)) := by
  unfold selectedPathValue
  simp only [finitePathValue, multiplyWeight]
  rw [selectedVertexWeight_tail]
  by_cases hzero : 0 ∈ times
  · rw [if_pos hzero]
    apply WithLp.ofLp_injective
    funext vertex
    change selectedVertexWeight bad times 0 vertex *
        ((normalizedMargulisFull ^ 40)
          (finitePathValue (normalizedMargulisFull ^ 40)
            (selectedVertexWeight bad
              (tailSelectedTimes times)))).ofLp vertex =
      bitAsReal (bad vertex) *
        ((normalizedMargulisFull ^ 40)
          (finitePathValue (normalizedMargulisFull ^ 40)
            (selectedVertexWeight bad
              (tailSelectedTimes times)))).ofLp vertex
    rw [selectedVertexWeight, if_pos hzero]
  · rw [if_neg hzero]
    apply WithLp.ofLp_injective
    funext vertex
    change selectedVertexWeight bad times 0 vertex *
        ((normalizedMargulisFull ^ 40)
          (finitePathValue (normalizedMargulisFull ^ 40)
            (selectedVertexWeight bad
              (tailSelectedTimes times)))).ofLp vertex =
      ((normalizedMargulisFull ^ 40)
        (finitePathValue (normalizedMargulisFull ^ 40)
          (selectedVertexWeight bad
            (tailSelectedTimes times)))).ofLp vertex
    rw [selectedVertexWeight, if_neg hzero]
    ring

theorem selectedPathValue_one
    {m : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool)
    (times : Finset (Fin 1)) (hnonempty : times.Nonempty) :
    selectedPathValue bad times = indicatorVector bad := by
  obtain ⟨time, htime⟩ := hnonempty
  have hzero : (0 : Fin 1) ∈ times := by
    simpa [Subsingleton.elim time 0] using htime
  unfold selectedPathValue
  simp only [finitePathValue]
  apply WithLp.ofLp_injective
  funext vertex
  change selectedVertexWeight bad times 0 vertex = bitAsReal (bad vertex)
  rw [selectedVertexWeight, if_pos hzero]

noncomputable def margulisOneVector {m : ℕ} [NeZero m] :
    EuclideanSpace ℝ (MargulisVertex m) :=
  WithLp.toLp 2 fun _ => 1

theorem normalizedMargulisFull_one
    {m : ℕ} [NeZero m] :
    normalizedMargulisFull (margulisOneVector (m := m)) =
      margulisOneVector := by
  apply WithLp.ofLp_injective
  funext vertex
  change margulisAdjacency (fun _ => (1 : ℝ)) vertex / 8 = 1
  rw [constant_margulisEigenvector]
  norm_num

theorem poweredMargulisFull_one
    {m : ℕ} [NeZero m] :
    (normalizedMargulisFull ^ 40) (margulisOneVector (m := m)) =
      margulisOneVector := by
  have hpower := normalizedMargulisFull_power_uniform 40
    (margulisOneVector (m := m))
  have huniform :
      uniformProjection (margulisOneVector (m := m)) =
        margulisOneVector := by
    apply WithLp.ofLp_injective
    funext vertex
    change (∑ _point : MargulisVertex m, (1 : ℝ)) /
        Fintype.card (MargulisVertex m) = 1
    have hcard : (Fintype.card (MargulisVertex m) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt Fintype.card_pos)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [huniform] at hpower
  exact hpower

theorem selectedPathValue_empty
    {m n : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool) :
    selectedPathValue bad (∅ : Finset (Fin n.succ)) =
      margulisOneVector := by
  induction n with
  | zero =>
      unfold selectedPathValue
      simp only [finitePathValue]
      apply WithLp.ofLp_injective
      funext vertex
      change selectedVertexWeight bad
        (∅ : Finset (Fin 1)) (0 : Fin 1) vertex = 1
      simp [selectedVertexWeight]
  | succ n ih =>
      rw [selectedPathValue_succ]
      simp only [Finset.notMem_empty, if_false]
      have htail :
          tailSelectedTimes (∅ : Finset (Fin (n + 2))) = ∅ := by
        ext time
        simp [tailSelectedTimes]
      rw [htail, ih, poweredMargulisFull_one]

theorem badProjection_one
    {m : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool) :
    badProjection bad (margulisOneVector (m := m)) =
      indicatorVector bad := by
  apply WithLp.ofLp_injective
  funext vertex
  change bitAsReal (bad vertex) * 1 = bitAsReal (bad vertex)
  ring

set_option maxHeartbeats 800000 in
-- Dependent path indices and operator powers need additional elaboration budget.
set_option maxRecDepth 100000 in
theorem selectedPathValue_compress
    {m n : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool)
    (times : Finset (Fin n.succ)) (hnonempty : times.Nonempty) :
    ∃ lead gaps,
      (∀ gap ∈ gaps, 0 < gap) ∧
      gaps.length = times.card - 1 ∧
      selectedPathValue bad times =
        ((normalizedMargulisFull ^ 40) ^ lead)
          (jointHitVector bad gaps) := by
  induction n with
  | zero =>
      have hzero : (0 : Fin 1) ∈ times := by
        obtain ⟨time, htime⟩ := hnonempty
        simpa [Subsingleton.elim time 0] using htime
      have hcard : times.card = 1 := by
        have htimes : times = Finset.univ := by
          ext time
          simp only [Finset.mem_univ, iff_true]
          simpa [Subsingleton.elim time 0] using hzero
        rw [htimes]
        simp
      refine ⟨0, [], by simp, by simp [hcard], ?_⟩
      rw [selectedPathValue_one bad times hnonempty]
      simp [jointHitVector]
  | succ n ih =>
      let tail := tailSelectedTimes times
      by_cases hzero : (0 : Fin (n + 2)) ∈ times
      · by_cases htail : tail.Nonempty
        · obtain ⟨lead, gaps, hpositive, hlength, heq⟩ :=
            ih tail htail
          refine ⟨0, lead.succ :: gaps, ?_, ?_, ?_⟩
          · intro gap hgap
            simp only [List.mem_cons] at hgap
            rcases hgap with rfl | hgap
            · omega
            · exact hpositive gap hgap
          · have hcard := card_tailSelectedTimes times
            rw [if_pos hzero] at hcard
            change tail.card = times.card - 1 at hcard
            simp only [List.length_cons]
            rw [hlength]
            have htailPositive : 0 < tail.card :=
              Finset.card_pos.mpr htail
            omega
          · rw [selectedPathValue_succ, if_pos hzero, heq]
            change badProjection bad
                ((normalizedMargulisFull ^ 40)
                  (((normalizedMargulisFull ^ 40) ^ lead)
                    (jointHitVector bad gaps))) =
              badProjection bad
                (((normalizedMargulisFull ^ 40) ^ lead.succ)
                  (jointHitVector bad gaps))
            congr 1
            rw [show ((normalizedMargulisFull ^ 40) ^ lead.succ) =
              (normalizedMargulisFull ^ 40) *
                ((normalizedMargulisFull ^ 40) ^ lead) by rw [pow_succ']]
            rfl
        · have htailEmpty : tail = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp htail
          have hcard := card_tailSelectedTimes times
          rw [if_pos hzero] at hcard
          change tail.card = times.card - 1 at hcard
          rw [htailEmpty] at hcard
          simp only [Finset.card_empty] at hcard
          have htimesPositive : 0 < times.card :=
            Finset.card_pos.mpr hnonempty
          have htimesCard : times.card = 1 := by omega
          refine ⟨0, [], by simp, by simp [htimesCard], ?_⟩
          change tailSelectedTimes times = ∅ at htailEmpty
          rw [selectedPathValue_succ, if_pos hzero, htailEmpty,
            selectedPathValue_empty, poweredMargulisFull_one,
            badProjection_one]
          simp [jointHitVector]
      · have htail : tail.Nonempty := by
          by_contra hnot
          have htailEmpty : tail = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp hnot
          have hcard := card_tailSelectedTimes times
          rw [if_neg hzero] at hcard
          change tail.card = times.card at hcard
          rw [htailEmpty] at hcard
          simp only [Finset.card_empty] at hcard
          have htimesPositive : 0 < times.card :=
            Finset.card_pos.mpr hnonempty
          omega
        obtain ⟨lead, gaps, hpositive, hlength, heq⟩ :=
          ih tail htail
        refine ⟨lead.succ, gaps, hpositive, ?_, ?_⟩
        · have hcard := card_tailSelectedTimes times
          rw [if_neg hzero] at hcard
          change tail.card = times.card at hcard
          rw [hlength, hcard]
        · rw [selectedPathValue_succ, if_neg hzero, heq]
          rw [show ((normalizedMargulisFull ^ 40) ^ lead.succ) =
            (normalizedMargulisFull ^ 40) *
              ((normalizedMargulisFull ^ 40) ^ lead) by rw [pow_succ']]
          rfl

theorem sum_normalizedMargulisFull
    {m : ℕ} [NeZero m]
    (value : EuclideanSpace ℝ (MargulisVertex m)) :
    (∑ vertex, (normalizedMargulisFull value).ofLp vertex) =
      ∑ vertex, value.ofLp vertex := by
  change (∑ vertex, margulisAdjacency value.ofLp vertex / 8) = _
  rw [← Finset.sum_div]
  rw [margulisAdjacency_sum]
  ring

theorem sum_normalizedMargulisFull_power
    {m : ℕ} [NeZero m]
    (iterations : ℕ)
    (value : EuclideanSpace ℝ (MargulisVertex m)) :
    (∑ vertex,
      ((normalizedMargulisFull ^ iterations) value).ofLp vertex) =
      ∑ vertex, value.ofLp vertex := by
  induction iterations with
  | zero => simp
  | succ iterations ih =>
      rw [show normalizedMargulisFull ^ iterations.succ =
        normalizedMargulisFull *
          normalizedMargulisFull ^ iterations by rw [pow_succ']]
      change (∑ vertex,
        (normalizedMargulisFull
          ((normalizedMargulisFull ^ iterations) value)).ofLp vertex) = _
      rw [sum_normalizedMargulisFull]
      exact ih

theorem sum_poweredMargulisOperator_power
    {m : ℕ} [NeZero m]
    (iterations : ℕ)
    (value : EuclideanSpace ℝ (MargulisVertex m)) :
    (∑ vertex,
      (((normalizedMargulisFull ^ 40) ^ iterations) value).ofLp vertex) =
      ∑ vertex, value.ofLp vertex := by
  rw [← pow_mul]
  exact sum_normalizedMargulisFull_power (40 * iterations) value

theorem selectedCondition_eq_jointHitOperatorProbability
    {m n : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool)
    (times : Finset (Fin n.succ)) (hnonempty : times.Nonempty) :
    ∃ gaps,
      (∀ gap ∈ gaps, 0 < gap) ∧
      gaps.length = times.card - 1 ∧
      booleanMean (fun sample : MargulisWalkSample m n.succ =>
        decide (∀ time ∈ times,
          concreteBadAt bad sample time = true)) =
        jointHitOperatorProbability bad gaps := by
  obtain ⟨lead, gaps, hpositive, hlength, heq⟩ :=
    selectedPathValue_compress bad times hnonempty
  refine ⟨gaps, hpositive, hlength, ?_⟩
  rw [booleanMean_selectedCondition_eq_pathValue]
  unfold jointHitOperatorProbability
  rw [heq, sum_poweredMargulisOperator_power]

def concreteBadTimes {m t : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool)
    (sample : MargulisWalkSample m t) : Finset (Fin t) :=
  Finset.univ.filter fun time => concreteBadAt bad sample time

def majorityThreshold (t : ℕ) : ℕ :=
  (t + 1) / 2

def concreteMajorityFailure {m t : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool)
    (sample : MargulisWalkSample m t) : Bool :=
  decide (majorityThreshold t ≤ (concreteBadTimes bad sample).card)

abbrev SelectedTimes (t : ℕ) :=
  {times : Finset (Fin t) // times.card = majorityThreshold t}

def selectedAllBad {m t : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool)
    (times : SelectedTimes t)
    (sample : MargulisWalkSample m t) : Bool :=
  decide (∀ time ∈ times.val, concreteBadAt bad sample time = true)

theorem selectedAllBad_spec {m t : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool)
    (times : SelectedTimes t)
    (sample : MargulisWalkSample m t) :
    selectedAllBad bad times sample = true ↔
      ∀ time ∈ times.val, concreteBadAt bad sample time = true := by
  simp [selectedAllBad]

theorem concreteMajorityFailure_covered {m t : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool)
    (sample : MargulisWalkSample m t)
    (hfailure : concreteMajorityFailure bad sample = true) :
    ∃ times : SelectedTimes t,
      selectedAllBad bad times sample = true := by
  have hcard :
      majorityThreshold t ≤ (concreteBadTimes bad sample).card := by
    exact of_decide_eq_true hfailure
  obtain ⟨times, hsubset, htimes⟩ :=
    Finset.exists_subset_card_eq hcard
  refine ⟨⟨times, htimes⟩, ?_⟩
  apply decide_eq_true
  intro time htime
  have hbadTimes : time ∈ concreteBadTimes bad sample :=
    hsubset htime
  exact (Finset.mem_filter.mp hbadTimes).2

theorem poweredMargulisNumericalBound :
    (5 * Real.sqrt 2 / 8) ^ 40 < (1 : ℝ) / 128 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    norm_num
  calc
    (5 * Real.sqrt 2 / 8) ^ 40 =
        (5 : ℝ) ^ 40 * ((Real.sqrt 2) ^ 2) ^ 20 / 8 ^ 40 := by ring
    _ = (5 : ℝ) ^ 40 * 2 ^ 20 / 8 ^ 40 := by rw [hsqrt]
    _ < (1 : ℝ) / 128 := by norm_num

theorem poweredMargulisEigenvalueBound
    (spectrum : ExpanderSpectrumContract)
    {m : ℕ} [NeZero m] {eigenvalue : ℝ}
    (heigenvalue : IsNontrivialMargulisEigenvalue
      (m := m) eigenvalue) :
    (|eigenvalue| / 8) ^ 40 < (1 : ℝ) / 128 := by
  have hbound := (spectrum m eigenvalue heigenvalue).1
  have hnonnegative : 0 ≤ |eigenvalue| / 8 := by positivity
  have hcomparison :
      |eigenvalue| / 8 ≤ 5 * Real.sqrt 2 / 8 := by
    exact div_le_div_of_nonneg_right hbound (by norm_num)
  exact (pow_le_pow_left₀ hnonnegative hcomparison 40).trans_lt
    poweredMargulisNumericalBound

theorem jointHitOperatorProbability_binary_le
    (spectrum : ExpanderSpectrumContract)
    {m : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool)
    (gaps : List ℕ) (hpositive : ∀ gap ∈ gaps, 0 < gap)
    (hrho : booleanMean bad ≤ (1 : ℝ) / 128) :
    jointHitOperatorProbability bad gaps ≤
      (1 / 128 : ℝ) * (1 / 64 : ℝ) ^ gaps.length := by
  have hrho0 : 0 ≤ booleanMean bad := by
    unfold booleanMean
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro vertex _
      cases bad vertex <;> simp [bitAsReal]
    · positivity
  have hsum :
      booleanMean bad + (5 * Real.sqrt 2 / 8) ^ 40 ≤
        (1 : ℝ) / 64 := by
    linarith [poweredMargulisNumericalBound]
  have hpow :
      (booleanMean bad + (5 * Real.sqrt 2 / 8) ^ 40) ^
          gaps.length ≤
        (1 / 64 : ℝ) ^ gaps.length := by
    apply pow_le_pow_left₀
    · exact add_nonneg hrho0 (by positivity)
    · exact hsum
  calc
    jointHitOperatorProbability bad gaps ≤
        booleanMean bad *
          (booleanMean bad + (5 * Real.sqrt 2 / 8) ^ 40) ^
            gaps.length :=
      jointHitOperatorProbability_le spectrum bad gaps hpositive
    _ ≤ (1 / 128 : ℝ) *
        (booleanMean bad + (5 * Real.sqrt 2 / 8) ^ 40) ^
          gaps.length := by
      apply mul_le_mul_of_nonneg_right hrho
      positivity
    _ ≤ (1 / 128 : ℝ) * (1 / 64 : ℝ) ^ gaps.length := by
      apply mul_le_mul_of_nonneg_left hpow
      norm_num

theorem majorityAmplificationNumericalBound
    (t : ℕ) (ht : Odd t) :
    (2 : ℝ) ^ t *
        ((1 / 128 : ℝ) *
          (1 / 64 : ℝ) ^ (majorityThreshold t - 1)) ≤
      1 / (2 : ℝ) ^ (2 * t + 4) := by
  obtain ⟨k, rfl⟩ := ht
  simp only [majorityThreshold]
  have hhalf : (2 * k + 1 + 1) / 2 - 1 = k := by omega
  rw [hhalf]
  have hpow :
      (4 : ℝ) ^ k * (1 / 64 : ℝ) ^ k = (1 / 16 : ℝ) ^ k := by
    rw [← mul_pow]
    norm_num
  calc
    (2 : ℝ) ^ (2 * k + 1) *
        ((1 / 128 : ℝ) * (1 / 64 : ℝ) ^ k) =
      (1 / 64 : ℝ) * ((4 : ℝ) ^ k * (1 / 64 : ℝ) ^ k) := by
        rw [pow_add, pow_mul]
        norm_num
        ring
    _ = (1 / 64 : ℝ) * (1 / 16 : ℝ) ^ k := by rw [hpow]
    _ ≤ 1 / (2 : ℝ) ^ (2 * (2 * k + 1) + 4) := by
      apply le_of_eq
      rw [show 2 * (2 * k + 1) + 4 = 4 * k + 6 by omega]
      rw [show 4 * k + 6 = 6 + 4 * k by omega, pow_add, pow_mul]
      norm_num
      rw [one_div_pow]
      ring

theorem concreteSelectedAllBad_le
    (spectrum : ExpanderSpectrumContract)
    {m t : ℕ} [NeZero m] (ht : 0 < t)
    (bad : MargulisVertex m → Bool)
    (choice : SelectedTimes t)
    (hrho : booleanMean bad ≤ (1 : ℝ) / 128) :
    booleanMean (selectedAllBad bad choice) ≤
      (1 / 128 : ℝ) *
        (1 / 64 : ℝ) ^ (majorityThreshold t - 1) := by
  cases t with
  | zero => omega
  | succ n =>
      have hcardPositive : 0 < choice.val.card := by
        rw [choice.property]
        unfold majorityThreshold
        omega
      have hnonempty : choice.val.Nonempty :=
        Finset.card_pos.mp hcardPositive
      obtain ⟨gaps, hpositive, hlength, heq⟩ :=
        selectedCondition_eq_jointHitOperatorProbability
          bad choice.val hnonempty
      change booleanMean (fun sample : MargulisWalkSample m n.succ =>
        decide (∀ time ∈ choice.val,
          concreteBadAt bad sample time = true)) ≤ _
      rw [heq]
      calc
        jointHitOperatorProbability bad gaps ≤
            (1 / 128 : ℝ) * (1 / 64 : ℝ) ^ gaps.length :=
          jointHitOperatorProbability_binary_le
            spectrum bad gaps hpositive hrho
        _ = (1 / 128 : ℝ) *
            (1 / 64 : ℝ) ^ (majorityThreshold n.succ - 1) := by
          rw [hlength, choice.property]

theorem bitAsReal_nonnegative (value : Bool) :
    0 ≤ bitAsReal value := by
  cases value <;> simp [bitAsReal]

theorem booleanMean_mono
    {Sample : Type} [Fintype Sample]
    (left right : Sample → Bool)
    (hpointwise : ∀ sample, left sample = true → right sample = true) :
    booleanMean left ≤ booleanMean right := by
  unfold booleanMean
  apply div_le_div_of_nonneg_right
  · apply Finset.sum_le_sum
    intro sample _
    cases hleft : left sample
    · exact bitAsReal_nonnegative (right sample)
    · have hright : right sample = true := hpointwise sample hleft
      simp [bitAsReal, hright]
  · positivity

/-- Uniform finite union bound, stated for Boolean events so that no measure
theory is trusted at this seam. -/
theorem booleanMean_unionBound
    {Sample Label : Type} [Fintype Sample] [Fintype Label]
    (target : Sample → Bool) (events : Label → Sample → Bool)
    (hcover : ∀ sample, target sample = true →
      ∃ label, events label sample = true) :
    booleanMean target ≤ ∑ label, booleanMean (events label) := by
  have hpointwise (sample : Sample) :
      bitAsReal (target sample) ≤
        ∑ label, bitAsReal (events label sample) := by
    cases htarget : target sample
    · simp [bitAsReal]
    · obtain ⟨label, hlabel⟩ := hcover sample htarget
      have hsingle :
          bitAsReal (events label sample) ≤
            ∑ candidate, bitAsReal (events candidate sample) := by
        exact Finset.single_le_sum
          (fun candidate _ => bitAsReal_nonnegative (events candidate sample))
          (Finset.mem_univ label)
      simpa [bitAsReal, htarget, hlabel] using hsingle
  unfold booleanMean
  calc
    (∑ sample, bitAsReal (target sample)) / Fintype.card Sample ≤
        (∑ sample, ∑ label, bitAsReal (events label sample)) /
          Fintype.card Sample := by
      apply div_le_div_of_nonneg_right
      · exact Finset.sum_le_sum fun sample _ => hpointwise sample
      · positivity
    _ = ∑ label,
        (∑ sample, bitAsReal (events label sample)) /
          Fintype.card Sample := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_div]

theorem booleanMean_unionBound_uniform
    {Sample Label : Type} [Fintype Sample] [Fintype Label]
    (target : Sample → Bool) (events : Label → Sample → Bool)
    (error : ℝ)
    (hcover : ∀ sample, target sample = true →
      ∃ label, events label sample = true)
    (hevents : ∀ label, booleanMean (events label) ≤ error) :
    booleanMean target ≤ Fintype.card Label * error := by
  calc
    booleanMean target ≤ ∑ label, booleanMean (events label) :=
      booleanMean_unionBound target events hcover
    _ ≤ ∑ _label : Label, error :=
      Finset.sum_le_sum fun label _ => hevents label
    _ = Fintype.card Label * error := by simp

/-- Abstract finite joint-hitting data.  This is below supplier strength: it
speaks only about one walk, one bad set, and one chosen collection of times. -/
structure JointHittingExperiment (Sample Time : Type)
    [Fintype Sample] [Fintype Time] where
  badAt : Sample → Time → Bool
  selected : Type
  selectedFintype : Fintype selected
  selectedTimes : selected → Finset Time
  selectedSize : ℕ
  selected_card : ∀ choice, (selectedTimes choice).card = selectedSize
  allBad : selected → Sample → Bool
  allBad_spec : ∀ choice sample,
    allBad choice sample = true ↔
      ∀ time ∈ selectedTimes choice, badAt sample time = true
  majorityFailure : Sample → Bool
  majorityCovered : ∀ sample, majorityFailure sample = true →
    ∃ choice, allBad choice sample = true

attribute [instance] JointHittingExperiment.selectedFintype

noncomputable def concreteJointHittingExperiment
    {m t : ℕ} [NeZero m]
    (bad : MargulisVertex m → Bool) :
    JointHittingExperiment (MargulisWalkSample m t) (Fin t) where
  badAt := concreteBadAt bad
  selected := SelectedTimes t
  selectedFintype := inferInstance
  selectedTimes := Subtype.val
  selectedSize := majorityThreshold t
  selected_card := Subtype.property
  allBad := selectedAllBad bad
  allBad_spec := selectedAllBad_spec bad
  majorityFailure := concreteMajorityFailure bad
  majorityCovered := concreteMajorityFailure_covered bad

theorem JointHittingExperiment.amplify
    {Sample Time : Type} [Fintype Sample] [Fintype Time]
    (experiment : JointHittingExperiment Sample Time)
    (jointError : ℝ)
    (hjoint : ∀ choice,
      booleanMean (experiment.allBad choice) ≤ jointError) :
    booleanMean experiment.majorityFailure ≤
      Fintype.card experiment.selected * jointError :=
  booleanMean_unionBound_uniform
    experiment.majorityFailure experiment.allBad jointError
    experiment.majorityCovered hjoint

theorem selectedFamily_le_twoPow
    {Sample Time : Type} [Fintype Sample] [Fintype Time]
    (experiment : JointHittingExperiment Sample Time)
    (hinjective :
      Function.Injective experiment.selectedTimes) :
    Fintype.card experiment.selected ≤ 2 ^ Fintype.card Time := by
  classical
  calc
    Fintype.card experiment.selected =
        (Finset.univ.image experiment.selectedTimes).card := by
      rw [Finset.card_image_of_injective _ hinjective]
      simp
    _ ≤ (Finset.univ.powerset).card := by
      apply Finset.card_le_card
      intro times htimes
      simp
    _ = 2 ^ Fintype.card Time := by simp

theorem concreteMajorityFailure_le
    (spectrum : ExpanderSpectrumContract)
    {m t : ℕ} [NeZero m]
    (ht : Odd t)
    (bad : MargulisVertex m → Bool)
    (hrho : booleanMean bad ≤ (1 : ℝ) / 128) :
    booleanMean (fun sample : MargulisWalkSample m t =>
      concreteMajorityFailure bad sample) ≤
      1 / (2 : ℝ) ^ (2 * t + 4) := by
  have htPositive : 0 < t := Odd.pos ht
  let experiment :
      JointHittingExperiment (MargulisWalkSample m t) (Fin t) :=
    concreteJointHittingExperiment bad
  have hamp :
      booleanMean experiment.majorityFailure ≤
        Fintype.card experiment.selected *
          ((1 / 128 : ℝ) *
            (1 / 64 : ℝ) ^ (majorityThreshold t - 1)) := by
    apply experiment.amplify
    intro choice
    exact concreteSelectedAllBad_le
      spectrum htPositive bad choice hrho
  have hfamilyNat :
      Fintype.card experiment.selected ≤ 2 ^ t := by
    have hbound := selectedFamily_le_twoPow experiment (by
      intro left right heq
      exact Subtype.ext heq)
    simpa [experiment] using hbound
  have hfamilyReal :
      (Fintype.card experiment.selected : ℝ) ≤ (2 : ℝ) ^ t := by
    exact_mod_cast hfamilyNat
  change booleanMean (fun sample : MargulisWalkSample m t =>
    concreteMajorityFailure bad sample) ≤ _
  calc
    booleanMean (fun sample : MargulisWalkSample m t =>
        concreteMajorityFailure bad sample) ≤
        Fintype.card experiment.selected *
          ((1 / 128 : ℝ) *
            (1 / 64 : ℝ) ^ (majorityThreshold t - 1)) := hamp
    _ ≤ (2 : ℝ) ^ t *
          ((1 / 128 : ℝ) *
            (1 / 64 : ℝ) ^ (majorityThreshold t - 1)) := by
      apply mul_le_mul_of_nonneg_right hfamilyReal
      positivity
    _ ≤ 1 / (2 : ℝ) ^ (2 * t + 4) :=
      majorityAmplificationNumericalBound t ht

/-- Package the concrete powered walk as the list-amplification contract used
by the supplier pipeline.  The input hypothesis is pointwise: the same fixed
walk works for every input without choosing advice from that input. -/
noncomputable def concretePoweredWalkListCertificate
    (spectrum : ExpanderSpectrumContract)
    {Input : Type} {m t : ℕ} [NeZero m]
    (ht : Odd t)
    (baseSucceeds : Input → MargulisVertex m → Bool)
    (hbase : ∀ input,
      booleanMean (fun vertex => !(baseSucceeds input vertex)) ≤
        (1 : ℝ) / 128) :
    AmplifiedListCertificate Input (MargulisWalkSample m t) where
  cardPositive := by
    let sample : MargulisWalkSample m t := {
      start := (0, 0)
      transitions := fun _ _ => 0
    }
    letI : Nonempty (MargulisWalkSample m t) := ⟨sample⟩
    exact Fintype.card_pos
  succeeds input sample :=
    !(concreteMajorityFailure
      (fun vertex => !(baseSucceeds input vertex)) sample)
  failure := 1 / (2 : ℝ) ^ (2 * t + 4)
  failureNonnegative := by positivity
  pointwise input := by
    simpa using concreteMajorityFailure_le spectrum ht
      (fun vertex => !(baseSucceeds input vertex)) (hbase input)

end NearCubicWires.SupplierWalk
