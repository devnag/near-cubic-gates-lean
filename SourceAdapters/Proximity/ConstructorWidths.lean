import SourceAdapters.Proximity.RequestSizes
import SourceAdapters.Proximity.TranslatedLengths

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": explicit width bounds for padded source labels,
renamed labels and paired auxiliary labels, used by the actual constructor. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicGates.Published.CW19Proximity
open QueryStep (paddedAddress)

def auxiliaryCap (q r : ℕ) : ℕ := 2 * (2 ^ r + blockVariableBound q + 1) ^ 2 + 2

def widthMeasure (q r B : ℕ) : ℕ :=
  B + auxiliaryCap q r + blockVariableBound q + 2 * q + 2 ^ q + r + 20

def widthDemand (q L r B : ℕ) : ℕ := widthMeasure q r B + L + predicateBlockBits q + 10

theorem arity_bits_source (S : SourceCircuit) : S.arity.bits.length ≤ (sourceCircuitWord S).length := by
  simp only [sourceCircuitWord, List.length_append, NearCubicWires.RepairOrdinary.frame_length]
  omega

theorem padded_bits {N : ℕ} (addresses : Fin N → Bool × ℕ) (B : ℕ)
    (hbits : ∀ i, (addresses i).2.bits.length ≤ B) (j : ℕ) :
    (paddedAddress addresses j).2.bits.length ≤ B := by
  unfold paddedAddress
  split
  · exact hbits _
  · simp

theorem doubled_lt_power (address B Wd : ℕ) (hbits : address.bits.length ≤ B) (hW : B + 1 ≤ Wd) :
    2 * address < 2 ^ Wd := by
  have ha : address < 2 ^ address.bits.length := by
    simpa only [Nat.size_eq_bits_len] using Nat.lt_size_self address
  have hb := ha.trans_le (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hbits)
  calc
    2 * address < 2 * 2 ^ B := Nat.mul_lt_mul_of_pos_left hb (by decide)
    _ = 2 ^ (B + 1) := by rw [pow_succ]; omega
    _ ≤ 2 ^ Wd := Nat.pow_le_pow_right (by decide) hW

theorem auxiliary_le {n q : ℕ} (V : NonadaptiveVerifier n q) (coins : Fin (2 ^ V.randomBits))
    (index : ℕ) (hi : index < blockVariableBound q) :
    2 * Nat.pair coins.val (index - q) + 1 ≤ auxiliaryCap q V.randomBits := by
  have hp := Nat.pair_lt_max_add_one_sq coins.val (index - q)
  have hc := coins.isLt
  have hm : max coins.val (index - q) + 1 ≤ 2 ^ V.randomBits + blockVariableBound q + 1 := by omega
  have hs := Nat.pow_le_pow_left hm 2
  unfold auxiliaryCap
  omega

theorem renamed_bitLength (address : Bool × ℕ) (B : ℕ) (hbits : address.2.bits.length ≤ B) :
    natBitLength (if address.1 then 2 * address.2 else address.2) ≤ B + 2 := by
  have hb := natBitLength_le_bits_succ address.2
  have hd := double_bits_length address.2
  have hdb := natBitLength_le_bits_succ (2 * address.2)
  cases address.1 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem global_bitLength {n q : ℕ} (V : NonadaptiveVerifier n q) (coins : Fin (2 ^ V.randomBits))
    (B : ℕ) (hbits : ∀ j, (addressPair (V.query coins j)).2.bits.length ≤ B)
    (index : ℕ) (hi : index < blockVariableBound q) :
    natBitLength (addressPair (localAddress V coins index)).2 ≤ B + auxiliaryCap q V.randomBits + 2 := by
  rw [← translated_address_pair]
  unfold AddressTranslation.translatedAddress
  split
  · exact (renamed_bitLength _ B (padded_bits _ B hbits index)).trans (by omega)
  · have ha := auxiliary_le V coins index hi
    have hb := natBitLength_le_bits_succ (2 * Nat.pair coins.val (index - q) + 1)
    have hs := bits_length_le (2 * Nat.pair coins.val (index - q) + 1)
    simp only
    omega

end NearCubicGates.Adapters.Proximity.SourceCallee
