import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Bool.Basic

/-!
# Splitting a permutation of paired slots into two matchings

The finite Hall argument supplies the two colors used in the Beneš
completeness induction (the proof of `lem:routing`). Edges retain their Boolean
slot, so parallel edges and the empty vertex type need no special cases.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing

/-- Every permutation of paired slots can be split into two permutations
of the pairs, by selecting one slot at each source and its complement. -/
theorem pair_splitting {α : Type*} [Finite α] (π : Equiv.Perm (α × Bool)) :
    ∃ b : α → Bool,
      Function.Bijective (fun a => (π (a, b a)).1) ∧
      Function.Bijective (fun a => (π (a, !(b a))).1) := by
  classical
  let neighbors : α → Finset α :=
    fun a => Finset.univ.image (fun c : Bool => (π (a, c)).1)
  have hall : ∀ s : Finset α, s.card ≤ (s.biUnion neighbors).card := by
    intro s
    have hcard : (s ×ˢ (Finset.univ : Finset Bool)).card ≤
        ((s.biUnion neighbors) ×ˢ (Finset.univ : Finset Bool)).card := by
      apply Finset.card_le_card_of_injOn π
      · intro p hp
        apply Finset.mem_product.mpr
        refine ⟨Finset.mem_biUnion.mpr
          ⟨p.1, (Finset.mem_product.mp hp).1, ?_⟩, Finset.mem_univ _⟩
        exact Finset.mem_image.mpr ⟨p.2, Finset.mem_univ _, rfl⟩
      · intro p _ q _ h
        exact π.injective h
    simp only [Finset.card_product, Finset.card_univ, Fintype.card_bool] at hcard
    omega
  obtain ⟨f, hf, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' neighbors).mp hall
  have edge : ∀ a, ∃ c : Bool, (π (a, c)).1 = f a := by
    intro a
    obtain ⟨c, _, hc⟩ := Finset.mem_image.mp (hmem a)
    exact ⟨c, hc⟩
  let b : α → Bool := fun a => Classical.choose (edge a)
  have hb (a : α) : (π (a, b a)).1 = f a := Classical.choose_spec (edge a)
  have first : Function.Bijective (fun a => (π (a, b a)).1) := by
    apply Finite.injective_iff_bijective.mp
    intro a c h
    apply hf
    simpa only [hb] using h
  have disjoint (a c : α) : π (a, !(b a)) ≠ π (c, b c) := by
    intro h
    have hp := π.injective h
    have ha : a = c := congrArg Prod.fst hp
    have hc : (!(b a)) = b c := congrArg Prod.snd hp
    subst c
    exact Bool.not_ne_self (b a) hc
  refine ⟨b, first, Finite.injective_iff_bijective.mp ?_⟩
  intro a c h
  obtain ⟨z, hz⟩ := first.2 (π (a, !(b a))).1
  have ha : (π (a, !(b a))).2 = !((π (z, b z)).2) := by
    apply Bool.eq_not_iff.mpr
    intro he
    exact disjoint a z (Prod.ext hz.symm he)
  have hc : (π (c, !(b c))).2 = !((π (z, b z)).2) := by
    apply Bool.eq_not_iff.mpr
    intro he
    exact disjoint c z (Prod.ext (h.symm.trans hz.symm) he)
  exact congrArg Prod.fst (π.injective (Prod.ext h (ha.trans hc.symm)))

end NearCubicGates.Adapters.Routing
