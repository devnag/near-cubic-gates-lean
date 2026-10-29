import SourceAdapters.Routing.NormalizedEmission

/-! The actual emitted sum vanishes on H exactly when all active item equations do. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing.RoutingPolynomial

variable {F : Type} [Field F] [CharP F 2]

def GuardedEquations (l : Layout) (e : Fin l.m → F) (a : F → F) : Prop :=
  ∀ v i, i ∈ routingItems l → patternHolds (i.guard l) v →
    evaluate l e a (cubeEval l.m e v) (i.expr l).poly = 0

theorem emission_iff_guarded (l : Layout) (e : Fin l.m → F) (coords : Coordinates l.m e)
    (hd : DisjointTerms (routingTerms l : List (Term l.m F))) (a : F → F) :
    (∀ z, InH l.m e z → evaluate l e a z (emit coords (routingTerms l)) = 0) ↔
      GuardedEquations l e a := by
  constructor
  · intro h v i hi hg
    have hz := h (cubeEval l.m e v) ⟨v,rfl⟩
    have hs := (Selectors.eval_emit_iff coords (routingTerms l) hd
      (fun w => match w with
        | none => cubeEval l.m e v
        | some b => a (cubeEval l.m e v + maskEval l.m e b)) v rfl).mp hz
    apply hs ⟨i.guard l,(i.expr l).poly⟩ _ hg
    exact List.mem_map.mpr ⟨i,hi,rfl⟩
  · intro h z hz
    obtain ⟨v,rfl⟩ := hz
    apply (Selectors.eval_emit_iff coords (routingTerms l) hd
      (fun w => match w with
        | none => cubeEval l.m e v
        | some b => a (cubeEval l.m e v + maskEval l.m e b)) v rfl).mpr
    intro t ht hg
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
    exact h v i hi hg

end NearCubicGates.Adapters.Routing.RoutingPolynomial
