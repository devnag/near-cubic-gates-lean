import SourceAdapters.Routing.CircuitFinal
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Variables

/-! The construction in `thm:embedding`: the actual finite bank-indexed
input vector evaluates the generic catalog as its emitted routing polynomial. -/
set_option autoImplicit false
noncomputable section
namespace NearCubicGates.Adapters.Routing.Circuit.Evaluation

variable {F : Type} [Field F]

/-- Input zero is X. Positive input j stores A(X+bank[j-1]). -/
def bankInputs (l : Layout) (e : Fin l.m → F) (A : F → F) (z : F) :
    Fin ((globalBank l).length+1) → F := fun j =>
  if j.val=0 then z else A (z + maskEval l.m e ((globalBank l).getD (j.val-1) 0))

theorem bankInputs_zero (l : Layout) (e : Fin l.m → F) (A : F → F) (z : F) :
    bankInputs l e A z ⟨0,by omega⟩ = z := by simp [bankInputs]

theorem bankInputs_encode (l : Layout) (e : Fin l.m → F) (A : F → F) (z : F)
    (v : Vars) (hv : match v with | none => True | some b => b ∈ globalBank l) :
    bankInputs l e A z (encodeVar l v) =
      match v with | none => z | some b => A (z + maskEval l.m e b) := by
  unfold bankInputs
  rw [encodeVar_val l v hv]
  cases v with
  | none => simp [readIndex]
  | some b =>
    simp [readIndex, Nat.add_comm 1, List.getD_eq_getElem?_getD, List.getElem?_idxOf hv]

/-- Only variables in the support need valid indices; unsupported encodeVar
fallbacks have no effect. Duplicate bank entries need no distinctness premise. -/
theorem eval_rename_supported (l : Layout) (e : Fin l.m → F) (A : F → F) (z : F)
    (p : MP F) (hp : Supports (globalBank l) p) :
    MvPolynomial.eval (bankInputs l e A z) (MvPolynomial.rename (encodeVar l) p) =
      evaluate l e A z p := by
  rw [MvPolynomial.eval_rename]
  apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
  intro v hv _
  cases v with
  | none => exact bankInputs_encode l e A z none trivial
  | some b => exact bankInputs_encode l e A z (some b) (hp _ hv)

/-- Exact evaluation of a compiled constraint: evaluation of the finite-input circuit polynomial
at the actual bank neighbors equals Routing.evaluate of its actual emitted sum. -/
theorem eval_compileTerms (l : Layout) (e : Fin l.m → F) (coords : Coordinates l.m e)
    (items : List (Item l.m F))
    (hr : ∀ item ∈ items, ReadsIn (globalBank l) item.2) (A : F → F) (z : F) :
    MvPolynomial.eval (bankInputs l e A z)
      ((compileTerms l e coords items).poly ((globalBank l).length+1)) =
      evaluate l e A z (emit coords (termList items)) := by
  have hc := compileTerms_correct l coords items hr
  rw [hc.2.2.1]
  exact eval_rename_supported l e A z _ hc.1


end NearCubicGates.Adapters.Routing.Circuit.Evaluation
end
