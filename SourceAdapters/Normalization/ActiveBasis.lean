import SourceAdapters.Normalization.ActiveConstraints
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# A square nonsingular set of active rows

For `lem:integer`, the active normals of a basic feasible point are reduced to
a basis. This is ordinary basis extraction from a spanning family, followed by
the standard equivalence between independent matrix rows and a nonzero determinant.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Normalization

open Matrix Module

variable {R ι κ : Type*} [Field R] [Fintype κ] [DecidableEq κ]

/-- A matrix with trivial right kernel has a square nonsingular selection of rows. -/
theorem exists_nonsingular_rows (A : Matrix ι κ R)
    (hsep : ∀ v : κ → R, (∀ i, A i ⬝ᵥ v = 0) → v = 0) :
    ∃ pick : κ → ι, Matrix.det (fun i j => A (pick i) j) ≠ 0 := by
  classical
  have hspan : Submodule.span R (Set.range A.row) = ⊤ := by
    by_contra hs
    obtain ⟨f, hf, hfker⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
      (lt_top_iff_ne_top.mpr hs) inferInstance
    let v := (dotProductEquiv R κ).symm f
    have hz : v = 0 := hsep v (by
      intro i
      have hmem : A i ∈ Submodule.span R (Set.range A.row) := Submodule.subset_span ⟨i, rfl⟩
      have hfi : f (A i) = 0 := by
        have hh : f (A i) ∈ (Submodule.span R (Set.range A.row)).map f :=
          ⟨A i, hmem, rfl⟩
        simpa only [hfker, Submodule.mem_bot] using hh
      have he : f (A i) = v ⬝ᵥ A i := by
        change f (A i) = (dotProductEquiv R κ) ((dotProductEquiv R κ).symm f) (A i)
        rw [LinearEquiv.apply_symm_apply]
      rw [he, dotProduct_comm] at hfi
      exact hfi)
    apply hf
    have hh := congrArg (dotProductEquiv R κ) hz
    simpa only [v, LinearEquiv.apply_symm_apply, map_zero] using hh
  let B := Basis.ofSpan hspan.ge
  let C : Basis κ R (κ → R) := B.reindex (B.indexEquiv (Pi.basisFun R κ))
  have hC : ∀ j : κ, C j ∈ Set.range A.row := by
    intro j
    apply Basis.ofSpan_subset hspan.ge
    refine ⟨(B.indexEquiv (Pi.basisFun R κ)).symm j, ?_⟩
    exact (B.reindex_apply (B.indexEquiv (Pi.basisFun R κ)) j).symm
  choose pick hpick using hC
  refine ⟨pick, ?_⟩
  have he : (fun i => A (pick i)) = C := funext hpick
  have hli : LinearIndependent R (fun i j => A (pick i) j) := by
    rw [he]
    exact C.linearIndependent
  exact ((Matrix.isUnit_iff_isUnit_det (fun i j => A (pick i) j)).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hli)).ne_zero

variable [LinearOrder R] [IsStrictOrderedRing R] [Fintype ι]

/-- A feasible finite pointed system has a feasible point determined by a square
nonsingular collection of its tight constraints. -/
theorem exists_active_basis (A : Matrix ι κ R) (b : ι → R)
    (hsep : ∀ v : κ → R, (∀ i, A i ⬝ᵥ v = 0) → v = 0)
    (hne : ∃ x : κ → R, ∀ i, b i ≤ A i ⬝ᵥ x) :
    ∃ (x : κ → R) (pick : κ → ι),
      (∀ i, b i ≤ A i ⬝ᵥ x) ∧ (∀ j, A (pick j) ⬝ᵥ x = b (pick j)) ∧
      Matrix.det (fun i j => A (pick i) j) ≠ 0 := by
  classical
  obtain ⟨x, hx, hactive⟩ := exists_active_separating
    (fun i => (dotProductEquiv R κ) (A i)) b hsep hne
  let I := {i : ι // A i ⬝ᵥ x = b i}
  obtain ⟨pick, hpick⟩ := exists_nonsingular_rows (fun (i : I) j => A i.1 j) (by
    intro v hv
    apply hactive v
    intro i hi
    exact hv ⟨i, hi⟩)
  exact ⟨x, fun j => (pick j).1, hx, fun j => (pick j).2, hpick⟩

end NearCubicGates.Adapters.Normalization
