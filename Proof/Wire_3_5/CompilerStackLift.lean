import Proof.Wire_3_5.Shared.S0
import Proof.Foundations.ThresholdCompiler

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires NearCubicWires.WireExponent3_5.Shared

/-! ## Stacking -/

def stackEquations {ZL ZR : Type} (H : ℤ) : List (SeparatedEquation ZL ZR) → SeparatedEquation ZL ZR
  | [] => ⟨fun _ => 0, fun _ => 0⟩
  | E :: Es => ⟨fun zl => E.left zl + H * (stackEquations H Es).left zl,
      fun zr => E.right zr + H * (stackEquations H Es).right zr⟩

/-- The value of a separated equation. -/
def eqValue {ZL ZR : Type} (E : SeparatedEquation ZL ZR) (zl : ZL) (zr : ZR) : ℤ := E.left zl + E.right zr

theorem holds_iff {ZL ZR : Type} (E : SeparatedEquation ZL ZR) (zl : ZL) (zr : ZR) :
    E.holds zl zr = true ↔ eqValue E zl zr = 0 := by
  simp [SeparatedEquation.holds, eqValue]

theorem stack_value {ZL ZR : Type} (H : ℤ) (E : SeparatedEquation ZL ZR) (Es : List (SeparatedEquation ZL ZR))
    (zl : ZL) (zr : ZR) :
    eqValue (stackEquations H (E :: Es)) zl zr = eqValue E zl zr + H * eqValue (stackEquations H Es) zl zr := by
  simp only [stackEquations, eqValue]; ring

theorem stack_holds_iff {ZL ZR : Type} (H V : ℤ) (hHV : V < H) (Es : List (SeparatedEquation ZL ZR))
    (zl : ZL) (zr : ZR) (hV : ∀ E ∈ Es, |eqValue E zl zr| ≤ V) :
    (stackEquations H Es).holds zl zr = true ↔ ∀ E ∈ Es, E.holds zl zr = true := by
  induction Es with
  | nil => simp [stackEquations, SeparatedEquation.holds]
  | cons E Es ih =>
    rw [holds_iff, stack_value]
    have ih' := ih (fun E' hE' => hV E' (List.mem_cons_of_mem _ hE'))
    rw [holds_iff] at ih'
    have hE := hV E List.mem_cons_self
    simp only [List.mem_cons, forall_eq_or_imp]
    rw [holds_iff, ← ih']
    constructor
    · intro h
      set w := eqValue (stackEquations H Es) zl zr
      by_cases hw : w = 0
      · refine ⟨by rw [hw] at h; linarith, hw⟩
      · exfalso
        have h1 : eqValue E zl zr = -(H * w) := by linarith
        have hV0 : 0 ≤ V := le_trans (abs_nonneg _) hE
        have hH0 : 0 < H := lt_of_le_of_lt hV0 hHV
        have h2 : H ≤ |H * w| := by
          rw [abs_mul, abs_of_pos hH0]
          have : 1 ≤ |w| := Int.one_le_abs hw
          nlinarith
        rw [h1, abs_neg] at hE
        linarith
    · rintro ⟨h1, h2⟩; rw [h1, h2]; ring

/-- The stacked value's magnitude: `|Σ H^{j−1}E_j| ≤ V·Σ_{j<t} H^j`. -/
theorem stack_value_abs_le {ZL ZR : Type} (H V : ℤ) (hH : 0 ≤ H) (Es : List (SeparatedEquation ZL ZR))
    (zl : ZL) (zr : ZR) (hV : ∀ E ∈ Es, |eqValue E zl zr| ≤ V) :
    |eqValue (stackEquations H Es) zl zr| ≤ V * ∑ j ∈ Finset.range Es.length, H ^ j := by
  induction Es with
  | nil => simp [stackEquations, eqValue]
  | cons E Es ih =>
    rw [stack_value, List.length_cons, Finset.sum_range_succ']
    have ih' := ih (fun E' hE' => hV E' (List.mem_cons_of_mem _ hE'))
    have hE := hV E List.mem_cons_self
    calc |eqValue E zl zr + H * eqValue (stackEquations H Es) zl zr|
        ≤ |eqValue E zl zr| + H * |eqValue (stackEquations H Es) zl zr| := by
          rw [← abs_of_nonneg hH]; rw [← abs_mul]; rw [abs_of_nonneg hH]; exact abs_add_le _ _
      _ ≤ V + H * (V * ∑ j ∈ Finset.range Es.length, H ^ j) := by gcongr
      _ = V * (∑ j ∈ Finset.range Es.length, H ^ (j + 1) + H ^ 0) := by
          have : ∑ j ∈ Finset.range Es.length, H ^ (j + 1) = H * ∑ j ∈ Finset.range Es.length, H ^ j := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
          rw [this]; ring

/-! ## The binomial lift -/

/-- `Σ_{J ∈ sublistsLen ℓ L} [∀ S ∈ J, G S] = C(#{S ∈ L : G S}, ℓ)`. -/
theorem sum_sublistsLen_all {β : Type} (G : β → Bool) :
    ∀ (ℓ : ℕ) (L : List β),
      ((L.sublistsLen ℓ).map fun J => bitZ (J.all G)).sum = ((L.filter G).length.choose ℓ : ℤ)
  | 0, L => by simp [bitZ]
  | ℓ + 1, [] => by simp
  | ℓ + 1, a :: L => by
    rw [List.sublistsLen_succ_cons, List.map_append, List.sum_append, List.map_map, sum_sublistsLen_all G (ℓ + 1) L]
    have : ((L.sublistsLen ℓ).map ((fun J => bitZ (J.all G)) ∘ List.cons a)) =
        (L.sublistsLen ℓ).map fun J => bitZ (G a) * bitZ (J.all G) := by
      apply List.map_congr_left
      intro J _
      simp only [Function.comp, List.all_cons]
      cases G a <;> cases J.all G <;> simp [bitZ]
    rw [this, List.sum_map_mul_left, sum_sublistsLen_all G ℓ L]
    by_cases hG : G a = true
    · simp only [List.filter_cons, hG, if_true, List.length_cons, Nat.choose_succ_succ', bitZ]
      push_cast; ring
    · simp only [List.filter_cons, hG, Bool.false_eq_true, if_false, bitZ]
      simp

def binLiftValue {β : Type} (Q : ℕ) (G : β → Bool) (L : List β) : ℤ :=
  ∑ j ∈ Finset.range Q, (-2 : ℤ) ^ j * ((L.sublistsLen (j + 1)).map fun J => bitZ (J.all G)).sum

/-- The lifted value is the base's numeric `binLift` at the number of true monomials. -/
theorem binLiftValue_eq {β : Type} (Q : ℕ) (G : β → Bool) (L : List β) :
    binLiftValue Q G L = ThresholdCompiler.binLift Q (L.filter G).length := by
  unfold binLiftValue ThresholdCompiler.binLift
  simp only [sum_sublistsLen_all]
  set t := (L.filter G).length
  rcases le_total Q t with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h]
    have hsplit := Finset.sum_range_add (fun j => (-2 : ℤ) ^ j * ((t.choose (j + 1) : ℕ) : ℤ)) t (Q - t)
    rw [Nat.add_sub_cancel' h] at hsplit
    rw [hsplit]
    have : ∑ x ∈ Finset.range (Q - t), (-2 : ℤ) ^ (t + x) * ((t.choose (t + x + 1) : ℕ) : ℤ) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    rw [this, add_zero]

theorem binLiftValue_modEq {β : Type} (Q : ℕ) (G : β → Bool) (L : List β) :
    binLiftValue Q G L ≡ (((L.filter G).length % 2 : ℕ) : ℤ) [ZMOD (2 : ℤ) ^ Q] := by
  rw [binLiftValue_eq]; exact ThresholdCompiler.binLiftModEqParity Q _

theorem binLift_count_le (Q M : ℕ) :
    ∑ j ∈ Finset.range Q, M.choose (j + 1) ≤ Q * max 1 M ^ Q := by
  calc ∑ j ∈ Finset.range Q, M.choose (j + 1) ≤ ∑ _j ∈ Finset.range Q, max 1 M ^ Q := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : j + 1 ≤ Q := Finset.mem_range.mp hj
        calc M.choose (j + 1) ≤ M ^ (j + 1) := Nat.choose_le_pow M (j + 1)
          _ ≤ max 1 M ^ (j + 1) := Nat.pow_le_pow_left (le_max_right 1 M) _
          _ ≤ max 1 M ^ Q := Nat.pow_le_pow_right (by omega) hj'
    _ = Q * max 1 M ^ Q := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

end NearCubicWires.WireExponent3_5.Compiler
