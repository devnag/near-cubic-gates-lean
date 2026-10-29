import SourceAdapters.Routing.PairMatching
import Mathlib.Logic.Equiv.Prod

/-!
# A pair-switch factorization of every permutation

The recursive Beneš step factors a permutation into input switches,
two permutations on the separate Boolean fibers, and output switches.
This is the the proof of `lem:routing` completeness step, with all slot choices
and the equality of the resulting permutation proved explicitly.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing

/-- Independently keep or swap the two slots of every pair. -/
def pairSwitch {α : Type*} (b : α → Bool) : Equiv.Perm (α × Bool) where
  toFun p := (p.1, Bool.xor p.2 (b p.1))
  invFun p := (p.1, Bool.xor p.2 (b p.1))
  left_inv := by
    rintro ⟨a, t⟩
    change (a, Bool.xor (Bool.xor t (b a)) (b a)) = (a, t)
    cases t <;> cases b a <;> rfl
  right_inv := by
    rintro ⟨a, t⟩
    change (a, Bool.xor (Bool.xor t (b a)) (b a)) = (a, t)
    cases t <;> cases b a <;> rfl

@[simp] theorem pairSwitch_apply {α : Type*} (b : α → Bool) (a : α) (t : Bool) :
    pairSwitch b (a, t) = (a, Bool.xor t (b a)) := rfl

theorem pairSwitch_involutive {α : Type*} (b : α → Bool) :
    Function.Involutive (pairSwitch b) :=
  (pairSwitch b).left_inv

theorem pairSwitch_bijective {α : Type*} (b : α → Bool) :
    Function.Bijective (pairSwitch b) :=
  (pairSwitch b).bijective

/-- Two independent permutations, preserving the Boolean fiber. -/
def pairMiddle {α : Type*} (π0 π1 : Equiv.Perm α) : Equiv.Perm (α × Bool) :=
  Equiv.prodCongrLeft (fun t : Bool => if t then π1 else π0)

@[simp] theorem pairMiddle_apply {α : Type*} (π0 π1 : Equiv.Perm α) (a : α) (t : Bool) :
    pairMiddle π0 π1 (a, t) = ((if t then π1 else π0) a, t) := rfl

@[simp] theorem pairMiddle_snd {α : Type*} (π0 π1 : Equiv.Perm α) (p : α × Bool) :
    (pairMiddle π0 π1 p).2 = p.2 := rfl

/-- Input pair switches, one permutation in each Boolean fiber, then
output pair switches realize the given permutation on every pair. -/
theorem pair_decomposition {α : Type*} [Finite α] (π : Equiv.Perm (α × Bool)) :
    ∃ (input output : α → Bool) (π0 π1 : Equiv.Perm α),
      π = ((pairSwitch input).trans (pairMiddle π0 π1)).trans (pairSwitch output) := by
  classical
  obtain ⟨b, hb0, hb1⟩ := pair_splitting π
  let π0 : Equiv.Perm α := Equiv.ofBijective (fun a => (π (a, b a)).1) hb0
  let π1 : Equiv.Perm α := Equiv.ofBijective (fun a => (π (a, !(b a))).1) hb1
  let output : α → Bool :=
    fun y => (π (π0.symm y, b (π0.symm y))).2
  have selected (a : α) : output (π0 a) = (π (a, b a)).2 := by
    simp only [output, Equiv.symm_apply_apply]
  have complementary (a : α) : (π (a, !(b a))).2 = !(output (π1 a)) := by
    apply Bool.eq_not_iff.mpr
    intro he
    have hfst : (π (a, !(b a))).1 =
        (π (π0.symm (π1 a), b (π0.symm (π1 a)))).1 := by
      change π1 a = π0 (π0.symm (π1 a))
      exact (π0.apply_symm_apply _).symm
    have hp := π.injective (Prod.ext hfst he)
    have ha : a = π0.symm (π1 a) := congrArg Prod.fst hp
    have ht : (!(b a)) = b (π0.symm (π1 a)) := congrArg Prod.snd hp
    rw [← ha] at ht
    exact Bool.not_ne_self (b a) ht
  have routes : ∀ p : α × Bool,
      pairSwitch output (pairMiddle π0 π1 p) = π (pairSwitch b p) := by
    rintro ⟨a, t⟩
    cases t
    · simp only [pairMiddle_apply, Bool.false_eq_true, ↓reduceIte, pairSwitch_apply, Bool.false_xor]
      exact Prod.ext rfl (selected a)
    · simp only [pairMiddle_apply, ↓reduceIte, pairSwitch_apply, Bool.true_xor]
      exact Prod.ext rfl (complementary a).symm
  refine ⟨b, output, π0, π1, ?_⟩
  apply Equiv.ext
  intro p
  change π p = pairSwitch output (pairMiddle π0 π1 (pairSwitch b p))
  exact (congrArg π (pairSwitch_involutive b p)).symm.trans (routes (pairSwitch b p)).symm

end NearCubicGates.Adapters.Routing
