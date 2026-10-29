import SourceAdapters.Routing.RoutingPatternsMask

/-! Every cube point has a full in-range layout address. No independence is needed. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing.Patterns

theorem cellMask_cover (l : Layout) (u : ℕ) (hu : u < l.h) :
    ∃ x s c r a, InRange l x s c r a ∧ cellMask l x s c r a = u := by
  have hh : l.h = 2 ^ l.k * (2 ^ l.ell * (2 ^ l.q * 16)) := by
    rw [LayoutFacts.h_eq]
    unfold Layout.C
    ring
  rw [hh] at hu
  have h1 : u / 2 ^ l.k < 2 ^ l.ell * (2 ^ l.q * 16) :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos l.k)).mpr (by simpa [Nat.mul_comm] using hu)
  have h2 : u / 2 ^ l.k / 2 ^ l.ell < 2 ^ l.q * 16 :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos l.ell)).mpr (by simpa [Nat.mul_comm] using h1)
  have h3 : u / 2 ^ l.k / 2 ^ l.ell / 2 ^ l.q < 16 :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos l.q)).mpr (by simpa [Nat.mul_comm] using h2)
  refine ⟨u % 2 ^ l.k, u / 2 ^ l.k % 2 ^ l.ell,
    u / 2 ^ l.k / 2 ^ l.ell % 2 ^ l.q,
    u / 2 ^ l.k / 2 ^ l.ell / 2 ^ l.q % 8,
    u / 2 ^ l.k / 2 ^ l.ell / 2 ^ l.q / 8, ?_, ?_⟩
  · exact ⟨Nat.mod_lt _ (Nat.two_pow_pos l.k), Nat.mod_lt _ (Nat.two_pow_pos l.ell),
      Nat.mod_lt _ (Nat.two_pow_pos l.q), Nat.mod_lt _ (by decide), by omega⟩
  · unfold cellMask
    rw [Nat.mod_add_div, Nat.mod_add_div, Nat.mod_add_div, Nat.mod_add_div]

theorem cube_bits_cell (l : Layout) (v : Fin l.m → Bool) :
    ∃ x s c r a, InRange l x s c r a ∧ bits l.m (cellMask l x s c r a) = v := by
  obtain ⟨x,s,c,r,a,h,he⟩ := cellMask_cover l (LayoutFacts.cubeMask v) (LayoutFacts.cubeMask_lt v)
  refine ⟨x,s,c,r,a,h,?_⟩
  rw [he]
  funext i
  exact LayoutFacts.cubeMask_testBit v i

theorem cube_label {F : Type} [Field F] (l : Layout) (e : Fin l.m → F) (v : Fin l.m → Bool) :
    ∃ x s c r a, InRange l x s c r a ∧ cubeEval l.m e v = label l e x s c r a := by
  obtain ⟨x,s,c,r,a,h,he⟩ := cube_bits_cell l v
  refine ⟨x,s,c,r,a,h,?_⟩
  rw [← he]
  rfl

end NearCubicGates.Adapters.Routing.Patterns
