import SourceAdapters.Routing.RoutingPatternsMask

/-! Route guards select exactly their stage, role, area, and column-mask class. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing.Patterns

theorem routePattern_iff (l : Layout) (x s c r a j role ck cv : ℕ)
    (h : InRange l x s c r a) (hj : j < 2 ^ l.ell) (hr : role < 8)
    (hck : ck < l.C) (hcv : cv < l.C) :
    patternHolds (routePattern l j role ck cv) (bits l.m (cellMask l x s c r a)) ↔
      s = j ∧ c &&& ck = cv &&& ck ∧ r = role ∧ a = 0 := by
  have hk : InRange l 0 (2 ^ l.ell - 1) ck 7 1 :=
    ⟨by positivity, by have := Nat.two_pow_pos l.ell; omega, hck, by decide, by decide⟩
  have hv : InRange l 0 j cv role 0 := ⟨by positivity, hj, hcv, hr, by decide⟩
  have hs : s &&& (2 ^ l.ell - 1) = s := Nat.and_two_pow_sub_one_of_lt_two_pow h.2.1
  have hj' : j &&& (2 ^ l.ell - 1) = j := Nat.and_two_pow_sub_one_of_lt_two_pow hj
  have hr' : r &&& 7 = r := Nat.and_two_pow_sub_one_of_lt_two_pow (n := 3) h.2.2.2.1
  have hrole : role &&& 7 = role := Nat.and_two_pow_sub_one_of_lt_two_pow (n := 3) hr
  have ha : a &&& 1 = a := Nat.and_two_pow_sub_one_of_lt_two_pow (n := 1) h.2.2.2.2
  rw [routePattern, patternMasks_iff _ _ _ _ (LayoutFacts.cellMask_lt l _ _ _ _ _ hk),
    cellMask_and l _ _ _ _ _ _ _ _ _ _ h hk,
    cellMask_and l _ _ _ _ _ _ _ _ _ _ hv hk]
  simp only [Nat.and_zero, Nat.zero_and, hs, hj', hr', hrole, ha]
  constructor
  · intro he
    have hl : InRange l 0 s (c &&& ck) r a :=
      ⟨by positivity, h.2.1, Nat.and_lt_two_pow c hck, h.2.2.2.1, h.2.2.2.2⟩
    have hv' : InRange l 0 j (cv &&& ck) role 0 :=
      ⟨by positivity, hj, Nat.and_lt_two_pow cv hck, hr, by decide⟩
    exact (LayoutFacts.cellMask_injective l _ _ _ _ _ _ _ _ _ _ hl hv' he).2
  · rintro ⟨rfl, hc, rfl, rfl⟩
    rw [hc]

end NearCubicGates.Adapters.Routing.Patterns
