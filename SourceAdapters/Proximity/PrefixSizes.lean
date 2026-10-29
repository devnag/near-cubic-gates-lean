import SourceAdapters.Proximity.LengthPrefix
import Proof.Gates.CounterMachine.PrefixRun

/-! Q04: polynomial Cells allocation from the paid logarithmic length prefix. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.LengthPrefix

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

def wrapped (word : List Bool) : List Bool := natWord word.length ++ word

theorem wrapped_leadOnes (word : List Bool) : leadOnes (wrapped word) = natBitLength word.length :=
  NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord _ _

theorem wrapped_length (word : List Bool) :
    (wrapped word).length = 2 * natBitLength word.length + 1 + word.length := by
  simp [wrapped]

theorem wrapped_length_bound (word : List Bool) : (wrapped word).length ≤ 3 * (word.length + 1) := by
  have hb := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le word.length
  rw [wrapped_length]
  omega

/-- Every width, call-length, or call-clock parameter has polynomial allocation. -/
theorem allocation_bound (a c : ℕ) (word : List Bool) :
    2 ^ (c * leadOnes (wrapped word)) * a ≤ (a * 2 ^ c) * (word.length + 1) ^ c := by
  rw [wrapped_leadOnes, Nat.mul_comm c, pow_mul]
  have hp := Nat.pow_le_pow_left
    (NearCubicGates.Close.CheckedPCPP.DescW.pow_bitlen_le word.length) c
  have hm := Nat.mul_le_mul_right a hp
  calc
    (2 ^ natBitLength word.length) ^ c * a ≤ (2 * word.length + 2) ^ c * a := hm
    _ = (a * 2 ^ c) * (word.length + 1) ^ c := by
      rw [show 2 * word.length + 2 = 2 * (word.length + 1) by omega, mul_pow]
      ring

/-- The linear allocation already supplies more than the raw input length. -/
theorem allocation_covers_length (word : List Bool) :
    word.length < 2 ^ leadOnes (wrapped word) := by
  rw [wrapped_leadOnes]
  exact Nat.lt_pow_succ_log_self (by decide) _

end NearCubicGates.Adapters.Proximity.LengthPrefix
