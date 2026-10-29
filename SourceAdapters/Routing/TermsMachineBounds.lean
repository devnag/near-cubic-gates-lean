import SourceAdapters.Routing.CoordinateMachineInputRun
import SourceAdapters.RAMACSP.GenEmit

/-! # Concrete capacities from the paid input preparation -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Bounds

open NearCubicWires
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Routing.CoordinateMachine

/-- Width of one packed bank or stack entry. -/
def wordWidth (rawN : ℕ) : ℕ := 16 * (rawN + 1)

/-- A common bound for circuit indices and their elementary arithmetic. -/
def arithmeticBound (rawN : ℕ) : ℕ := 100 * (rawN + 1) ^ 2

theorem raw_le_arithmetic (rawN : ℕ) : rawN + 3 ≤ arithmeticBound rawN := by
  unfold arithmeticBound
  nlinarith

theorem width_le_arithmetic (rawN : ℕ) : wordWidth rawN + 3 ≤ arithmeticBound rawN := by
  unfold wordWidth arithmeticBound
  nlinarith

theorem product_le_arithmetic (rawN k : ℕ) (hk : k ≤ rawN) :
    wordWidth rawN * k + 3 ≤ arithmeticBound rawN := by
  have hp := Nat.mul_le_mul_left (wordWidth rawN) hk
  unfold wordWidth arithmeticBound at *
  nlinarith

theorem prepared_large (word : List Bool) :
    let G := globOf (preparedInput word)
    arithmeticBound word.length + 3 ≤ G.K ∧ G.K = G.N := by
  intro G
  have hp := prepared_K_power_lower word
  have hs : 1 ≤ (word.length + 1) ^ 2 := by
    have hh : 0 < (word.length + 1) ^ 2 := by positivity
    omega
  have h26 : (word.length + 1) ^ 2 ≤ (word.length + 1) ^ 6 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  have hbig : arithmeticBound word.length + 3 ≤ 2 * (2 * word.length + 2) ^ 6 := by
    calc arithmeticBound word.length + 3 ≤ 128 * (word.length + 1) ^ 2 := by
           unfold arithmeticBound; omega
      _ ≤ 128 * (word.length + 1) ^ 6 := Nat.mul_le_mul_left _ h26
      _ = 2 * (2 * word.length + 2) ^ 6 := by ring
  exact ⟨hbig.trans hp, rfl⟩

theorem prepared_arithmetic_cap (word : List Bool) :
    arithmeticBound word.length ≤ (globOf (preparedInput word)).cap := by
  have hk := (prepared_large word).1
  have hc := cap_ge (globOf (preparedInput word))
  omega

theorem prepared_width (word : List Bool) :
    wordWidth word.length + 2 ≤ (globOf (preparedInput word)).K := by
  have hh := width_le_arithmetic word.length
  have hk := (prepared_large word).1
  omega

theorem prepared_product (word : List Bool) (k : ℕ) (hk : k ≤ word.length) :
    wordWidth word.length * k ≤ (globOf (preparedInput word)).K := by
  have hh := product_le_arithmetic word.length k hk
  have hK := (prepared_large word).1
  omega

theorem prepared_pow (word : List Bool) (a : ℕ) (ha : a ≤ wordWidth word.length) :
    2 ^ a ≤ (globOf (preparedInput word)).cap := by
  have hk := prepared_width word
  have hp := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (show a < (globOf (preparedInput word)).K by omega)
  have hc := cap_add (globOf (preparedInput word))
  omega

theorem prepared_pack (word : List Bool) (xs : List ℕ) (hlen : xs.length ≤ word.length)
    (hwords : ∀ x ∈ xs, x < 2 ^ wordWidth word.length) :
    packW (wordWidth word.length) xs ≤ (globOf (preparedInput word)).cap := by
  have hlt := packW_lt (wordWidth word.length) xs hwords
  have hk := prepared_product word xs.length hlen
  have hp := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
  have hc := cap_add (globOf (preparedInput word))
  omega

theorem prepared_natBitLength (word : List Bool) (f v : ℕ) (hf : f ≤ word.length)
    (hv : v ≤ max (arithmeticBound word.length) (2 ^ f)) :
    natBitLength v + 2 ≤ (globOf (preparedInput word)).K := by
  have hK := (prepared_large word).1
  by_cases hm : v ≤ arithmeticBound word.length
  · have hb : natBitLength v ≤ v + 1 := by
      unfold natBitLength
      have := Nat.log_le_self 2 v
      omega
    omega
  · have hvf : v ≤ 2 ^ f := by omega
    have hp : v < 2 ^ (f + 1) := by
      have hh := Nat.two_pow_pos f
      rw [pow_succ]
      omega
    have hb := NearCubicGates.Adapters.RAMACSP.Gen.natBitLength_le_of_lt (by omega : 1 ≤ f + 1) hp
    have hr := raw_le_arithmetic word.length
    omega

theorem prepared_value_cap (word : List Bool) (f v : ℕ) (hf : f ≤ word.length)
    (hv : v ≤ max (arithmeticBound word.length) (2 ^ f)) :
    v ≤ (globOf (preparedInput word)).cap := by
  have ha := prepared_arithmetic_cap word
  have hp := prepared_pow word f (by unfold wordWidth; omega)
  omega

end NearCubicGates.Adapters.Routing.TermsMachine.Bounds
