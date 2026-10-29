import SourceAdapters.Routing.LayoutMask
import Mathlib.Tactic.Ring

/-!
The construction in `app:affine-embedding`: disjoint lane/stage/column/role/area blocks give bounded,
injective labels, with XOR acting separately on every block.-/
set_option autoImplicit false
noncomputable section

namespace NearCubicGates.Adapters.Routing.LayoutFacts

theorem block_xor (n a₁ a₂ b₁ b₂ : ℕ) (h₁ : a₁ < 2^n) (h₂ : a₂ < 2^n) :
    (a₁+2^n*b₁) ^^^ (a₂+2^n*b₂) = (a₁^^^a₂)+2^n*(b₁^^^b₂) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.add_comm a₁, Nat.add_comm a₂, Nat.add_comm (a₁^^^a₂),
    Nat.testBit_two_pow_mul_add _ h₁, Nat.testBit_two_pow_mul_add _ h₂,
    Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow h₁ h₂)]
  split <;> simp [Nat.testBit_xor]

theorem block_injective (n a₁ a₂ b₁ b₂ : ℕ) (h₁ : a₁ < 2^n) (h₂ : a₂ < 2^n)
    (h : a₁+2^n*b₁ = a₂+2^n*b₂) : a₁=a₂ ∧ b₁=b₂ := by
  have hm := congrArg (fun a => a % 2^n) h
  have hd := congrArg (fun a => a / 2^n) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at hm
  simp only [Nat.add_mul_div_left _ _ (Nat.two_pow_pos n), Nat.div_eq_of_lt h₁,
    Nat.div_eq_of_lt h₂, Nat.zero_add] at hd
  exact ⟨hm,hd⟩

theorem block_lt (n a b N : ℕ) (ha : a < 2^n) (hb : b < N) : a+2^n*b < 2^n*N := by
  calc
    a+2^n*b < 2^n+2^n*b := Nat.add_lt_add_right ha _
    _ = 2^n*(b+1) := by ring
    _ ≤ 2^n*N := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hb)

theorem h_eq (l : Layout) : l.h = 16 * 2^l.k * 2^l.ell * l.C := by
  simp only [Layout.h, Layout.m, Layout.C, pow_add]
  ring

theorem cellMask_lt (l : Layout) (x s c r a : ℕ) (h : InRange l x s c r a) :
    cellMask l x s c r a < l.h := by
  rcases h with ⟨hx,hs,hc,hr,ha⟩
  have hra : r+8*a < 16 := by omega
  have hcol := block_lt l.q c (r+8*a) 16 hc hra
  have hstage := block_lt l.ell s (c+2^l.q*(r+8*a)) (2^l.q*16) hs hcol
  have hwhole := block_lt l.k x (s+2^l.ell*(c+2^l.q*(r+8*a)))
    (2^l.ell*(2^l.q*16)) hx hstage
  rw [h_eq]
  change x+2^l.k*(s+2^l.ell*(c+2^l.q*(r+8*a))) < 16*2^l.k*2^l.ell*2^l.q
  convert hwhole using 1
  ring

theorem cellMask_xor (l : Layout) (x s c r a x' s' c' r' a' : ℕ)
    (h : InRange l x s c r a) (h' : InRange l x' s' c' r' a') :
    cellMask l x s c r a ^^^ cellMask l x' s' c' r' a' =
      cellMask l (x^^^x') (s^^^s') (c^^^c') (r^^^r') (a^^^a') := by
  unfold cellMask
  rw [block_xor l.k _ _ _ _ h.1 h'.1, block_xor l.ell _ _ _ _ h.2.1 h'.2.1,
    block_xor l.q _ _ _ _ h.2.2.1 h'.2.2.1]
  have hr := block_xor 3 r r' a a' h.2.2.2.1 h'.2.2.2.1
  norm_num at hr
  rw [hr]

theorem cellMask_injective (l : Layout) (x s c r a x' s' c' r' a' : ℕ)
    (h : InRange l x s c r a) (h' : InRange l x' s' c' r' a')
    (he : cellMask l x s c r a = cellMask l x' s' c' r' a') :
    x=x' ∧ s=s' ∧ c=c' ∧ r=r' ∧ a=a' := by
  unfold cellMask at he
  obtain ⟨hx,he⟩ := block_injective l.k _ _ _ _ h.1 h'.1 he
  obtain ⟨hs,he⟩ := block_injective l.ell _ _ _ _ h.2.1 h'.2.1 he
  obtain ⟨hc,he⟩ := block_injective l.q _ _ _ _ h.2.2.1 h'.2.2.1 he
  obtain ⟨hr,ha⟩ := block_injective 3 _ _ _ _ h.2.2.2.1 h'.2.2.2.1 he
  exact ⟨hx,hs,hc,hr,ha⟩

theorem inRange_xor (l : Layout) (x s c r a x' s' c' r' a' : ℕ)
    (h : InRange l x s c r a) (h' : InRange l x' s' c' r' a') :
    InRange l (x^^^x') (s^^^s') (c^^^c') (r^^^r') (a^^^a') :=
  ⟨Nat.xor_lt_two_pow h.1 h'.1, Nat.xor_lt_two_pow h.2.1 h'.2.1,
    Nat.xor_lt_two_pow h.2.2.1 h'.2.2.1,
    Nat.xor_lt_two_pow (n := 3) h.2.2.2.1 h'.2.2.2.1,
    Nat.xor_lt_two_pow (n := 1) h.2.2.2.2 h'.2.2.2.2⟩

variable {F : Type} [Field F]

theorem label_add [CharP F 2] (l : Layout) (e : Fin l.m → F) (x s c r a x' s' c' r' a' : ℕ)
    (h : InRange l x s c r a) (h' : InRange l x' s' c' r' a') :
    label l e x s c r a + label l e x' s' c' r' a' =
      label l e (x^^^x') (s^^^s') (c^^^c') (r^^^r') (a^^^a') := by
  rw [label, label, ← maskEval_xor, cellMask_xor l _ _ _ _ _ _ _ _ _ _ h h']
  rfl

theorem label_eq_iff (l : Layout) (e : Fin l.m → F) (hi : Independent l.m e)
    (x s c r a x' s' c' r' a' : ℕ) (h : InRange l x s c r a) (h' : InRange l x' s' c' r' a') :
    label l e x s c r a = label l e x' s' c' r' a' ↔
      x=x' ∧ s=s' ∧ c=c' ∧ r=r' ∧ a=a' := by
  constructor
  · intro he
    exact cellMask_injective l _ _ _ _ _ _ _ _ _ _ h h'
      (maskEval_injective l.m e hi _ _ (cellMask_lt l _ _ _ _ _ h) (cellMask_lt l _ _ _ _ _ h') he)
  · rintro ⟨rfl,rfl,rfl,rfl,rfl⟩
    rfl

theorem label_mem (l : Layout) (e : Fin l.m → F) (x s c r a : ℕ) :
    InH l.m e (label l e x s c r a) := maskEval_mem l.m e _

end NearCubicGates.Adapters.Routing.LayoutFacts
