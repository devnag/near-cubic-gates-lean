import SourceAdapters.Proximity.TaggedCalls
import NineInputs

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": polynomial closure for the proved source dispatcher,
charged in its own tagged request word. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TaggedCalls

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Published.CW19Proximity

theorem budget_bound (K A e d L : ℕ) (hK : K ≤ A) (he : e ≤ d) (hd : 1 ≤ d) :
    2 * (32 * L + K * (L + 1) ^ e + 22) + 2 ≤ (100 + 2 * A) * (L + 2) ^ d := by
  have hp : (L + 1) ^ e ≤ (L + 2) ^ d :=
    (Nat.pow_le_pow_left (by omega) e).trans (Nat.pow_le_pow_right (by omega) he)
  have hl : L + 1 ≤ (L + 2) ^ d := (by omega : L + 1 ≤ L + 2).trans (Nat.le_self_pow (by omega : d ≠ 0) _)
  have ht := Nat.mul_le_mul hK hp
  nlinarith

theorem polynomial {A B : Type} (ia oa : A → List Bool) (ib ob : B → List Bool)
    (left : SourcePolyTime ia oa) (right : SourcePolyTime ib ob) :
    SourcePolyTime (input ia ib) (payload oa ob) := by
  obtain ⟨K1, e1, ⟨P⟩⟩ := left
  obtain ⟨K2, e2, ⟨Q⟩⟩ := right
  refine ⟨100 + 2 * (K1 + K2), max 1 (max e1 e2), ⟨(wordFunction P Q).enlargeBudget ?_⟩⟩
  intro r
  cases r with
  | inl a =>
    simpa only [cost, input, payload, selectedBudget, Sum.elim_inl, List.length_cons, Nat.add_assoc]
      using budget_bound K1 (K1 + K2) e1 (max 1 (max e1 e2)) (ia a).length
        (by omega) ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _)
  | inr b =>
    simpa only [cost, input, payload, selectedBudget, Sum.elim_inr, List.length_cons, Nat.add_assoc]
      using budget_bound K2 (K1 + K2) e2 (max 1 (max e1 e2)) (ib b).length
        (by omega) ((le_max_right _ _).trans (le_max_right _ _)) (le_max_left _ _)

end NearCubicGates.Adapters.Proximity.TaggedCalls
