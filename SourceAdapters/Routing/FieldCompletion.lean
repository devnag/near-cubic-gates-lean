import SourceAdapters.Routing.FieldCompletionData
import SourceAdapters.Routing.BenesCompleteness

/-! Completion of all routing columns with fixed endpoint records, preserving
 every field point outside the exact routing-writable set. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing.FieldCompletion

variable {F : Type} [Field F] [CharP F 2]

theorem table_local (l : Layout) (e : Fin l.m → F) (he : Independent l.m e)
    (s : Settings l.k) (hs : Coherent l.k s) (U : Lane l.k → Fin l.C → F)
    (hU : ∀ x c, IsBit (U x c)) (background : F → F) :
    LocalRouting l e (table l e s U background) := by
  have sc : switchCount l.k < 2*l.k := by
    have := l.k_pos
    unfold switchCount
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hj x c
    rw [table_data l e he s U background j hj x c]
    exact rows_bit l s U hU j x c
  · intro j hj x c
    rw [table_switch l e he s U background j hj x c]
    cases s j x <;> simp [IsBit]
  · intro j hj x c c'
    rw [table_switch l e he s U background j hj x c,
      table_switch l e he s U background j hj x c']
  · intro j hj x c
    rw [table_switch l e he s U background j hj _ c,
      table_switch l e he s U background j hj x c, hs j hj x]
  · intro j hj x c
    have hj' : j < 2*l.k := lt_trans hj sc
    have hjn : j+1 < 2*l.k := by omega
    rw [table_data l e he s U background j hj' x c,
      table_data l e he s U background (j+1) hjn x c,
      table_data l e he s U background (j+1) hjn _ c,
      table_switch l e he s U background j hj x c]
    apply (FieldSoundness.routing_equation_iff (s j x) _ _ _).mpr
    have ht := rows_transport l s hs U j hj x c
    cases hbool : s j x <;> simpa only [stageMap, hbool, Bool.false_eq_true,
      ↓reduceIte] using ht

/-- All payload columns use one Beneš permutation. Only the data and switch
cells declared by RoutingWritable are changed, even outside the affine cube. -/
theorem fieldRoutingCompletion (l : Layout) (e : Fin l.m → F)
    (he : Independent l.m e) : FieldRoutingCompletion l e := by
  intro U V hU _hV hUV background
  obtain ⟨π,hπ⟩ := hUV
  obtain ⟨s,hs,hpath⟩ := Completeness.benesCompleteness l.k l.k_pos π
  have sc : switchCount l.k < 2*l.k := by
    have := l.k_pos
    unfold switchCount
    omega
  have hz : 0 < 2*l.k := by have := l.k_pos; omega
  refine ⟨table l e s U background, table_local l e he s hs U hU background,
    ?_, ?_, table_preserves l e s U background⟩
  · intro x c
    rw [table_data l e he s U background 0 hz x c]
    rfl
  · intro x c
    rw [table_data l e he s U background (switchCount l.k) sc x c]
    obtain ⟨y,rfl⟩ := π.surjective x
    have ht := congrFun (Soundness.path_transport l.k s (Fin l.C → F)
      (rows l s U) (fun j hj x => funext (rows_transport l s hs U j hj x)) y) c
    rw [hpath y] at ht
    exact ht.trans (hπ y c).symm

end NearCubicGates.Adapters.Routing.FieldCompletion
