import SourceAdapters.Routing.SelectorsValues
import SourceAdapters.Routing.SelectorsBounds

/-! Disjoint normalized guards prevent cancellation between simultaneous errors.
This proves the exact generic emission interface for arbitrary catalogs.
-/
set_option autoImplicit false
noncomputable section
open Classical

namespace NearCubicGates.Adapters.Routing.Selectors

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem disjoint_cons {m : ℕ} (t : Term m F) (ts : List (Term m F))
    (hd : DisjointTerms (t :: ts)) :
    DisjointTerms ts ∧ ∀ u ∈ ts, ∀ v,
      ¬ (patternHolds t.guard v ∧ patternHolds u.guard v) := by
  constructor
  · intro i j hij v h
    apply hd ⟨i.val + 1, by simp⟩ ⟨j.val + 1, by simp⟩
      (by intro he; apply hij; apply Fin.ext; have := congrArg Fin.val he; dsimp at this; omega) v
    simpa using h
  · intro u hu v h
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hu
    apply hd ⟨0, by simp⟩ ⟨i + 1, by simp; omega⟩ (by intro h'; have := congrArg Fin.val h'; dsimp at this; omega) v
    simpa [he] using h

theorem eval_emit_cons {m : ℕ} {e : Fin m → F} (coords : Coordinates m e)
    (t : Term m F) (ts : List (Term m F)) (reads : Vars → F) (v : Fin m → Bool)
    (h : reads none = cubeEval m e v) :
    MvPolynomial.eval reads (emit coords (t :: ts)) =
      (if patternHolds t.guard v then MvPolynomial.eval reads t.equation else 0) +
        MvPolynomial.eval reads (emit coords ts) := by
  change MvPolynomial.eval reads (selector coords t.guard * t.equation + emit coords ts) = _
  rw [map_add, map_mul, eval_selector coords t.guard reads v h]
  split_ifs <;> simp

theorem eval_emit_iff {m : ℕ} {e : Fin m → F} (coords : Coordinates m e)
    (ts : List (Term m F)) (hd : DisjointTerms ts)
    (reads : Vars → F) (v : Fin m → Bool) (h : reads none = cubeEval m e v) :
    MvPolynomial.eval reads (emit coords ts) = 0 ↔
      ∀ t ∈ ts, patternHolds t.guard v → MvPolynomial.eval reads t.equation = 0 := by
  induction ts with
  | nil => simp [emit]
  | cons t ts ih =>
    obtain ⟨htail, hhead⟩ := disjoint_cons t ts hd
    by_cases hp : patternHolds t.guard v
    · have hz : MvPolynomial.eval reads (emit coords ts) = 0 := by
        apply (ih htail).mpr
        intro u hu hpu
        exact False.elim (hhead u hu v ⟨hp, hpu⟩)
      rw [eval_emit_cons coords t ts reads v h, if_pos hp, hz, add_zero]
      constructor
      · intro he u hu hpu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact he
        · exact False.elim (hhead u hu v ⟨hp, hpu⟩)
      · intro he
        exact he t (by simp) hp
    · rw [eval_emit_cons coords t ts reads v h, if_neg hp, zero_add, ih htail]
      constructor
      · intro he u hu hpu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact False.elim (hp hpu)
        · exact he u hu hpu
      · intro he u hu hpu
        exact he u (by simp [hu]) hpu

theorem normalizedEmission : NormalizedEmission (F := F) := by
  intro m _ e coords ts hd ht
  refine ⟨degree_emit coords ts _ ht, ?_⟩
  intro v reads h
  exact eval_emit_iff coords ts hd reads v h

end NearCubicGates.Adapters.Routing.Selectors
