import SourceAdapters.Routing.LayoutPacking

/-! Exact natural-mask interpretation of the pattern selectors.-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing.Patterns

def bits (m u : ℕ) : Fin m → Bool := fun i => u.testBit i.val

theorem patternMasks_iff (m known value u : ℕ) (hk : known < 2 ^ m) :
    patternHolds (patternMasks m known value) (bits m u) ↔
      u &&& known = value &&& known := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hi : i < m
    · cases hb : known.testBit i
      · simp
      · simp only [Bool.and_true]
        exact h ⟨i, hi⟩ (value.testBit i) (by simp [patternMasks, hb])
    · have hb : known.testBit i = false :=
        Nat.testBit_lt_two_pow (hk.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hb]
  · intro h i b hb
    unfold patternMasks at hb
    split_ifs at hb with hk
    · have hv : value.testBit i.val = b := Option.some.inj hb
      have he := congrArg (fun z : ℕ => z.testBit i.val) h
      simp only [Nat.testBit_and, hk, Bool.and_true] at he
      exact he.trans hv

theorem block_and (n a₁ a₂ b₁ b₂ : ℕ) (h₁ : a₁ < 2 ^ n) (h₂ : a₂ < 2 ^ n) :
    (a₁ + 2 ^ n * b₁) &&& (a₂ + 2 ^ n * b₂) =
      (a₁ &&& a₂) + 2 ^ n * (b₁ &&& b₂) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.add_comm a₁, Nat.add_comm a₂, Nat.add_comm (a₁ &&& a₂),
    Nat.testBit_two_pow_mul_add _ h₁, Nat.testBit_two_pow_mul_add _ h₂,
    Nat.testBit_two_pow_mul_add _ (Nat.and_lt_two_pow a₁ h₂)]
  split <;> simp [Nat.testBit_and]

theorem cellMask_and (l : Layout) (x s c r a x' s' c' r' a' : ℕ)
    (h : InRange l x s c r a) (h' : InRange l x' s' c' r' a') :
    cellMask l x s c r a &&& cellMask l x' s' c' r' a' =
      cellMask l (x &&& x') (s &&& s') (c &&& c') (r &&& r') (a &&& a') := by
  unfold cellMask
  rw [block_and l.k _ _ _ _ h.1 h'.1, block_and l.ell _ _ _ _ h.2.1 h'.2.1,
    block_and l.q _ _ _ _ h.2.2.1 h'.2.2.1]
  have hr := block_and 3 r r' a a' h.2.2.2.1 h'.2.2.2.1
  norm_num at hr
  rw [hr]

end NearCubicGates.Adapters.Routing.Patterns
