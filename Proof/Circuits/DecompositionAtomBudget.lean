import Proof.Circuits.DecompositionAtomRun

/-! Polynomial budget in the physical native bit width. This bounds the
executed serializer/pair charges without expanding any magnitude to unary. -/
namespace NearCubicWires.RepairOrdinary.DecompositionAtom
open CanonicalBinary PCPSerializerMass
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def envelope (width : ℕ) := 1000000000000000000*(width+1)^12

theorem magnitude_bits (n : ℕ) : (encodeNat n).bits.length ≤ 3*(natBitLength n+1)^5 := by
  let w := natBitLength n
  have h := (nat_bits_width (encodeNat n)).trans (encodeNat_bits_le n)
  have hp : 1≤(w+1)^5 := Nat.one_le_pow 5 _ (by omega)
  have hm : 1+2*w^4*(w+1) ≤ 1+2*(w+1)^5 := by
    calc
      _ ≤ 1+2*(w+1)^4*(w+1) := by gcongr; omega
      _ = _ := by ring
  change (encodeNat n).bits.length ≤ 3*(w+1)^5
  change (encodeNat n).bits.length ≤ 1+2*w^4*(w+1) at h
  omega

theorem budget_envelope (z : ℤ) : budget z ≤ envelope (natBitLength z.natAbs) := by
  let w := natBitLength z.natAbs
  let bits := (encodeNat z.natAbs).bits
  let b := decide (z<0)
  have hbits : bits.length ≤ 3*(w+1)^5 := magnitude_bits _
  have h1 : 1≤(w+1)^5 := Nat.one_le_pow 5 _ (by omega)
  have h5 : (w+1)^5≤(w+1)^12 := pow_le_pow_right₀ (by omega) (by omega)
  have h10 : (w+1)^10≤(w+1)^12 := pow_le_pow_right₀ (by omega) (by omega)
  have hw : w≤(w+1)^12 := by
    calc
      w ≤ (w+1)^1 := by simp
      _ ≤ (w+1)^12 := pow_le_pow_right₀ (by omega) (by omega)
  have hpair := PCPPairCanonical.budget_quadratic [b] bits
  have hsize : 1+bits.length+1 ≤ 5*(w+1)^5 := by omega
  have hpair' : PCPPairCanonical.budget [b] bits ≤ 51200*(w+1)^10 := by
    calc
      _ ≤ 2048*(1+bits.length+1)^2 := hpair
      _ ≤ 2048*(5*(w+1)^5)^2 := by gcongr
      _ = _ := by ring
  have hserializer : PCPTraversal.budget (3*w) ≤ 531441000000000000*(w+1)^12 := by
    unfold PCPTraversal.budget
    calc
      _ ≤ 1000000000000*(3*(w+1))^12 := by gcongr; omega
      _ = _ := by rw [mul_pow]; norm_num; ring
  change 20*w+(PCPTraversal.budget (3*w)+1+
    (PCPPairCanonical.budget [b] bits+4*bits.length+10))+28 ≤ 1000000000000000000*(w+1)^12
  omega

end NearCubicWires.RepairOrdinary.DecompositionAtom
