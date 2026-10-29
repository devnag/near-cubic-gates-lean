import SourceAdapters.Routing.LayoutPacking

/-!
The construction in `app:affine-embedding`: literal carry masks implement predecessor and cyclic
column successor, including the last column and zero-width-free branches.-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing.LayoutFacts

theorem pow_xor_mask (t : ℕ) : 2^t ^^^ (2^(t+1)-1) = 2^t-1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor,Nat.testBit_two_pow,Nat.testBit_two_pow_sub_one,Nat.testBit_two_pow_sub_one]
  by_cases h : t=i
  · subst i; simp
  · have he : (i<t+1) ↔ i<t := by omega
    simp [h,he]

theorem lowMask_xor_mask (t : ℕ) : (2^t-1) ^^^ (2^(t+1)-1) = 2^t := by
  have h := congrArg (fun x => x ^^^ (2^(t+1)-1)) (pow_xor_mask t)
  simpa [Nat.xor_assoc] using h.symm

theorem predecessor_xor (t x : ℕ) (hx : x % 2^(t+1) = 2^t) :
    x ^^^ (2^(t+1)-1) = x-1 := by
  have hp := Nat.two_pow_pos t
  have hP := Nat.two_pow_pos (t+1)
  have ht : 2^t < 2^(t+1) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hrepr : x = 2^t+2^(t+1)*(x/2^(t+1)) := by
    simpa [hx] using (Nat.mod_add_div x (2^(t+1))).symm
  calc
    x ^^^ (2^(t+1)-1) = (2^t+2^(t+1)*(x/2^(t+1))) ^^^ ((2^(t+1)-1)+2^(t+1)*0) := by rw [←hrepr];simp
    _ = (2^t ^^^ (2^(t+1)-1))+2^(t+1)*((x/2^(t+1))^^^0) :=
      block_xor (t+1) _ _ _ _ ht (by omega)
    _ = x-1 := by rw [pow_xor_mask,Nat.xor_zero];omega

theorem mod_next_of_bit_false (t c : ℕ) (hl : c % 2^t = 2^t-1) (hb : c.testBit t = false) :
    c % 2^(t+1) = 2^t-1 := by
  have hd : c / 2^t % 2 = 0 := by
    apply Nat.mod_two_eq_zero_iff_testBit_zero.mpr
    simpa only [Nat.testBit_div_two_pow,Nat.zero_add] using hb
  have hdiv : c % 2^(t+1) / 2^t = 0 := by
    rw [pow_succ,Nat.mod_mul_right_div_self,hd]
  have hmod : c % 2^(t+1) % 2^t = 2^t-1 := by
    rw [pow_succ,Nat.mod_mul_right_mod,hl]
  have he := Nat.mod_add_div (c%2^(t+1)) (2^t)
  simpa [hdiv,hmod] using he.symm

theorem successor_xor (t c : ℕ) (hc : c % 2^(t+1) = 2^t-1) :
    c ^^^ (2^(t+1)-1) = c+1 := by
  have hp := Nat.two_pow_pos t
  have hP := Nat.two_pow_pos (t+1)
  have ht : 2^t < 2^(t+1) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hrepr : c = (2^t-1)+2^(t+1)*(c/2^(t+1)) := by
    simpa [hc] using (Nat.mod_add_div c (2^(t+1))).symm
  calc
    c ^^^ (2^(t+1)-1) = ((2^t-1)+2^(t+1)*(c/2^(t+1))) ^^^ ((2^(t+1)-1)+2^(t+1)*0) := by rw [←hrepr];simp
    _ = ((2^t-1) ^^^ (2^(t+1)-1))+2^(t+1)*((c/2^(t+1))^^^0) :=
      block_xor (t+1) _ _ _ _ (by omega) (by omega)
    _ = c+1 := by rw [lowMask_xor_mask,Nat.xor_zero];omega

theorem column_xor_successor (q t c : ℕ) (hc : c<2^q) (h : ColumnCase q t c) :
    c ^^^ (2^(t+1)-1) = (c+1)%2^q := by
  rcases h with ⟨ht,hl,hb⟩
  by_cases htop : t+1<q
  · have hbit := hb htop
    rw [successor_xor t c (mod_next_of_bit_false t c hl hbit)]
    apply (Nat.mod_eq_of_lt _).symm
    have hn : c ≠ 2^q-1 := by
      intro he
      rw [he,Nat.testBit_two_pow_sub_one] at hbit
      simp [ht] at hbit
    omega
  · have hq : q=t+1 := by omega
    subst q
    have hp := Nat.two_pow_pos t
    have hP := Nat.two_pow_pos (t+1)
    have hd : c/2^t < 2 := by
      rw [Nat.div_lt_iff_lt_mul hp]
      simpa [pow_succ,Nat.mul_comm] using hc
    have he := Nat.mod_add_div c (2^t)
    have htwo : ∀ d : ℕ, d<2 → d=0 ∨ d=1 := by omega
    have hd' : c/2^t=0 ∨ c/2^t=1 := htwo _ hd
    rcases hd' with hd' | hd'
    · have he' : c=2^t-1 := by simpa [hl,hd'] using he.symm
      rw [he',lowMask_xor_mask,Nat.sub_add_cancel (by omega)]
      exact (Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))).symm
    · have he' : c=2^(t+1)-1 := by
        simp only [hl,hd',Nat.mul_one] at he
        rw [pow_succ]
        omega
      rw [he',Nat.xor_self,Nat.sub_add_cancel (by omega),Nat.mod_self]

end NearCubicGates.Adapters.Routing.LayoutFacts
