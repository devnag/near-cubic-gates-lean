import SourceAdapters.Routing.LayoutPacking

/-!
The construction in `app:affine-embedding`: ordinary LSB digits are scattered into the column and low
lane blocks. -/
set_option autoImplicit false
noncomputable section
namespace NearCubicGates.Adapters.Routing.LayoutFacts

def scatter (i p : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => scatter i p n ^^^ (if i.testBit n then 2^(p+n) else 0)

theorem testBit_scatter (i p n b : ℕ) :
    (scatter i p n).testBit b =
      (decide (p≤b) && decide (b<p+n) && i.testBit (b-p)) := by
  induction n with
  | zero =>
    simp only [scatter,Nat.zero_testBit,Nat.add_zero]
    by_cases h : b<p <;> simp [h]
  | succ n ih =>
    rw [scatter,Nat.testBit_xor,ih]
    by_cases hb : b=p+n
    · subst b
      have : p+n-p=n := by omega
      split <;> simp_all
    · have he : (if i.testBit n then 2^(p+n) else 0).testBit b=false := by
        split
        · rw [Nat.testBit_two_pow];simp;omega
        · simp
      rw [he,Bool.xor_false]
      have he' : (b<p+(n+1)) ↔ b<p+n := by omega
      simp [he']

theorem scatter_eq (i p n : ℕ) : scatter i p n = 2^p*(i%2^n) := by
  apply Nat.eq_of_testBit_eq
  intro b
  have he := Nat.testBit_two_pow_mul_add (i%2^n) (Nat.two_pow_pos p) b
  rw [Nat.add_zero] at he
  rw [testBit_scatter,he]
  by_cases h : b<p
  · simp [h]
  · simp only [h,if_false,Nat.testBit_mod_two_pow]
    have h₁ : p≤b := by omega
    have he' : b-p<n ↔ b<p+n := by omega
    simp [h₁,he']

theorem input_quotient_lt (l : Layout) (omega m i : ℕ) (ho : omega≤m)
    (hm : m-omega≤l.k-1) (hi : i<2^m) : i/2^omega<2^(l.k-1) := by
  have hc : i/2^omega<2^(m-omega) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos omega),←Nat.pow_add,Nat.sub_add_cancel ho]
    exact hi
  exact hc.trans_le (Nat.pow_le_pow_right (by decide) hm)

theorem input_lane_lt (l : Layout) (omega m i : ℕ) (ho : omega≤m)
    (hm : m-omega≤l.k-1) (hi : i<2^m) : 2^(l.k-1)+i/2^omega<2^l.k := by
  have hq := input_quotient_lt l omega m i ho hm hi
  have hk := l.k_pos
  have he : 2^l.k=2^(l.k-1)+2^(l.k-1) := by
    rw [←Nat.two_mul,←Nat.pow_succ'];congr 1;omega
  omega

theorem input_range (l : Layout) (omega m i : ℕ) (hq : omega≤l.q) (ho : omega≤m)
    (hm : m-omega≤l.k-1) (hi : i<2^m) :
    InRange l (2^(l.k-1)+i/2^omega) 0 (i%2^omega) 0 0 :=
  ⟨input_lane_lt l omega m i ho hm hi,Nat.two_pow_pos _,
    (Nat.mod_lt i (Nat.two_pow_pos omega)).trans_le (Nat.pow_le_pow_right (by decide) hq),
    by decide,by decide⟩

def inputMask (l : Layout) (omega m i : ℕ) : ℕ :=
  2^(l.k-1) ^^^ scatter i (l.k+l.ell) omega ^^^ scatter (i/2^omega) 0 (m-omega)

theorem inputMask_eq (l : Layout) (omega m i : ℕ) (ho : omega≤m)
    (hm : m-omega≤l.k-1) (hi : i<2^m) :
    inputMask l omega m i = cellMask l (2^(l.k-1)+i/2^omega) 0 (i%2^omega) 0 0 := by
  have hc : i/2^omega<2^(m-omega) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos omega),←Nat.pow_add,Nat.sub_add_cancel ho]
    exact hi
  have hcT := input_quotient_lt l omega m i ho hm hi
  unfold inputMask cellMask
  rw [scatter_eq,scatter_eq,Nat.pow_zero,Nat.one_mul,Nat.mod_eq_of_lt hc]
  simp only [Nat.mul_zero,Nat.add_zero]
  have e₁ : 2^(l.k-1) ^^^ i/2^omega = 2^(l.k-1)+i/2^omega := by
    have he := block_xor (l.k-1) 0 (i/2^omega) 1 0 (Nat.two_pow_pos _) hcT
    simpa [Nat.add_comm] using he
  have e₂ : (2^(l.k-1)+i/2^omega) ^^^ 2^(l.k+l.ell)*(i%2^omega) =
      2^(l.k-1)+i/2^omega+2^l.k*(2^l.ell*(i%2^omega)) := by
    have he := block_xor l.k (2^(l.k-1)+i/2^omega) 0 0 (2^l.ell*(i%2^omega))
      (input_lane_lt l omega m i ho hm hi) (Nat.two_pow_pos _)
    simpa [pow_add,Nat.mul_assoc] using he
  rw [Nat.xor_assoc,Nat.xor_comm (2^(l.k+l.ell)*(i%2^omega)),←Nat.xor_assoc,e₁,e₂]
  ring

variable {F : Type} [Field F] [CharP F 2]

theorem maskEval_scatter (m : ℕ) (e : Fin m → F) (i p n : ℕ) :
    maskEval m e (scatter i p n) =
      ∑ j : Fin n, if i.testBit j.val then maskEval m e (2^(p+j.val)) else 0 := by
  induction n with
  | zero => simp [scatter,maskEval_zero]
  | succ n ih =>
    rw [scatter,maskEval_xor,ih,Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    congr 1
    split <;> simp_all [maskEval_zero]

end NearCubicGates.Adapters.Routing.LayoutFacts
