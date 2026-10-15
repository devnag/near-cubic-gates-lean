import Proof.Gates.Interfaces.CounterFormats

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicGates.Close.Interfaces
open NearCubicWires.RepairRepresentation (natWord)

/-- Halve while even and the exponent is positive. -/
def red : ℕ → ℕ → ℕ × ℕ
  | a, 0 => (a, 0)
  | a, e + 1 => if a % 2 = 0 then red (a / 2) e else (a, e + 1)

theorem red_val : ∀ (a e : ℕ), ((red a e).1 : ℚ) / 2 ^ (red a e).2 = (a : ℚ) / 2 ^ e
  | a, 0 => by simp [red]
  | a, e + 1 => by
    unfold red
    split_ifs with h
    · rw [red_val (a / 2) e]
      have ha : (a : ℚ) = 2 * ((a / 2 : ℕ) : ℚ) := by
        have : a = 2 * (a / 2) := by omega
        exact_mod_cast this
      rw [ha, pow_succ]; field_simp
    · rfl

theorem red_cop : ∀ (a e : ℕ), (red a e).2 = 0 ∨ (red a e).1 % 2 = 1
  | a, 0 => by simp [red]
  | a, e + 1 => by
    unfold red
    split_ifs with h
    · exact red_cop (a / 2) e
    · right; simp; omega

theorem red_le : ∀ (a e : ℕ), (red a e).1 ≤ a ∧ (red a e).2 ≤ e
  | a, 0 => by simp [red]
  | a, e + 1 => by
    unfold red
    split_ifs with h
    · have := red_le (a / 2) e; omega
    · simp

theorem ratWord_red (a e : ℕ) :
    ratWord ((a : ℚ) / 2 ^ e) = natWord 0 ++ natWord (red a e).1 ++ natWord (2 ^ (red a e).2) := by
  rw [← red_val a e]
  set a' := (red a e).1
  set e' := (red a e).2
  have hcop : Nat.Coprime a' (2 ^ e') := by
    rcases red_cop a e with h | h
    · rw [show e' = 0 from h]; simp
    · exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr h))
  have hq : ((a' : ℚ) / 2 ^ e') = ((a' : ℤ) : ℚ) / (((2 ^ e' : ℕ) : ℤ) : ℚ) := by push_cast; rfl
  have hb : (0 : ℤ) < ((2 ^ e' : ℕ) : ℤ) := by positivity
  have hc : Nat.Coprime (a' : ℤ).natAbs ((2 ^ e' : ℕ) : ℤ).natAbs := by simpa using hcop
  have hnum := Rat.num_div_eq_of_coprime hb hc
  have hden := Rat.den_div_eq_of_coprime hb hc
  unfold ratWord Interfaces.intWord
  rw [hq, hnum]
  have hden' : (((a' : ℤ) : ℚ) / (((2 ^ e' : ℕ) : ℤ) : ℚ)).den = 2 ^ e' := by exact_mod_cast hden
  rw [hden']
  simp

/-- The interval of eq:output from `S = Σ_certain N_y`, `U = N_unc`, `k`, `n`. -/
def ivl (S U k n : ℕ) : ℚ × ℚ :=
  (((S + 2 ^ (k - 1) * U : ℕ) : ℚ) / 2 ^ n, ((2 ^ (k - 1) * U : ℕ) : ℚ) / 2 ^ n)

theorem outputWord_ivl (S U k n : ℕ) :
    outputWord (ivl S U k n) = (natWord 0 ++ natWord (red (S + 2 ^ (k - 1) * U) n).1 ++
      natWord (2 ^ (red (S + 2 ^ (k - 1) * U) n).2)) ++ (natWord 0 ++ natWord (red (2 ^ (k - 1) * U) n).1 ++
      natWord (2 ^ (red (2 ^ (k - 1) * U) n).2)) := by
  unfold outputWord ivl
  rw [ratWord_red, ratWord_red]

end NearCubicGates.Close.CounterMachine
