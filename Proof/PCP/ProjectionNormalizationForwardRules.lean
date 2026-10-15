import Proof.PCP.ProjectionNormalizationCursorRestore

/-! Motion checks for the clause comparator and its concrete composition.
These discharge the cursor-restoration premise from actual rule tables. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.CursorRestore
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem composition_forward {t a b : ℕ} (p : Machine t a) (q : Machine t b) (i : Fin t)
    (hp : NoLeft p i) (hq : NoLeft q i) : NoLeft (Composition.machine p q) i := by
  intro state
  refine Fin.addCases (fun c bits x hx => ?_) (fun c bits x hx => ?_) state
  · by_cases hh : p.halted c=true
    · simp [Composition.machine,hh] at hx
      subst x
      simp [Composition.bridge]
    · cases hr : p.rule c bits with
      | none => simp [Composition.machine,hh,hr] at hx
      | some y =>
        simp [Composition.machine,hh,hr] at hx
        subst x
        exact hp c bits y hr
  · cases hr : q.rule c bits with
    | none => simp [Composition.machine,hr] at hx
    | some y =>
      simp [Composition.machine,hr] at hx
      subst x
      exact hq c bits y hr

theorem focus_forward {t u s : ℕ} (slots : Fin t → Fin u) (hinj : Function.Injective slots)
    (p : Machine t s) (i : Fin t) (hp : NoLeft p i) : NoLeft (RecoveryFocus.machine slots p) (slots i) := by
  intro state bits x hx
  cases hr : p.rule state (bits ∘ slots) with
  | none => simp [RecoveryFocus.machine,hr] at hx
  | some y =>
    simp [RecoveryFocus.machine,hr] at hx
    subst x
    simpa only [RecoveryFocus.action,RecoveryFocus.pick_slot slots hinj] using hp state (bits ∘ slots) y hr

theorem field_forward (i : Fin 3) : NoLeft FieldEquality.machine i := by
  intro state bits x hx
  cases hs : FieldEquality.code.symm state with
  | inl same =>
    simp only [FieldEquality.machine,hs] at hx
    split at hx <;> cases hx <;> fin_cases i <;> simp [FieldEquality.action] <;> split <;> simp
  | inr stage =>
    cases stage with
    | inl flags =>
      rcases flags with ⟨same,left,right⟩
      simp only [FieldEquality.machine,hs,Option.some.injEq] at hx
      subst x
      fin_cases i <;> simp [FieldEquality.action] <;> split <;> simp
    | inr final => simp [FieldEquality.machine,hs] at hx

theorem clause_forward (i : Fin 3) : NoLeft ClauseEquality.machine i :=
  composition_forward FieldEquality.machine ClauseEquality.tailMachine i (field_forward i)
    (composition_forward FieldEquality.machine FieldEquality.machine i (field_forward i) (field_forward i))

end NearCubicWires.RepairSource.ProjectionNormalization.CursorRestore
