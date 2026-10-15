import Proof.PCP.PCPPRequestTaggedCons

/-! Fixed tagged-list depth keeps both byte width and paid pair cost small. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestTaggedCons
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem pair_bits (a b : ℕ) : (Nat.pair a b).bits.length≤2*(a.bits.length+b.bits.length+1) := by
  have hf := PCPPair.pair_bound a.bits b.bits
  rw [CanonicalPositiveOutput.nat_bits_value,CanonicalPositiveOutput.nat_bits_value] at hf
  exact CanonicalPositiveOutput.nat_bits_length_le _ _ hf

theorem cons_bits (a b : ℕ) :
    (Nat.pair 1 (Nat.pair a b)).bits.length≤8*(a.bits.length+b.bits.length+1) := by
  have h := pair_bits 1 (Nat.pair a b)
  have hp := pair_bits a b
  change (Nat.pair 1 (Nat.pair a b)).bits.length≤2*(1+(Nat.pair a b).bits.length+1) at h
  omega

theorem budget_quadratic (a b : ℕ) :
    budget a b ≤ 65536*(a.bits.length+b.bits.length+1)^2 := by
  let m := a.bits.length+b.bits.length+1
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hinner := PCPPairCanonical.budget_quadratic a.bits b.bits
  have hp := pair_bits a b
  have houter := PCPPairCanonical.budget_quadratic (1 : ℕ).bits (Nat.pair a b).bits
  have hsize : 1+(Nat.pair a b).bits.length+1≤4*m := by dsimp [m]; omega
  have ho : PCPPairCanonical.budget (1 : ℕ).bits (Nat.pair a b).bits≤32768*m^2 := by
    calc
      _ ≤ 2048*(1+(Nat.pair a b).bits.length+1)^2 := houter
      _ ≤ 2048*(4*m)^2 := by gcongr
      _ = 32768*m^2 := by ring
  change PCPPairCanonical.budget a.bits b.bits+4+10+
    PCPPairCanonical.budget (1 : ℕ).bits (Nat.pair a b).bits≤65536*m^2
  change PCPPairCanonical.budget a.bits b.bits≤2048*m^2 at hinner
  nlinarith

end NearCubicWires.RepairOrdinary.PCPPRequestTaggedCons
