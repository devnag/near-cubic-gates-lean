import Proof.Amplification.RecoveryVerifierSound

/-! Universal runtime of the actual cold verifier. Its dependence on an
arbitrary witness is linear; the canonical certificate supplies the cubic
witness-length bound needed by the final encoded NP record. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdVerifier
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RecoveryColdAllCode
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_bound (bits word : List Bool) :
    budget bits word≤4398046511104*(bits.length+1)^4+64*word.length+1024 := by
  have hf := RecoveryColdFront.front_budget bits word
  have hq := RecoveryAllCode.budget_le (width bits)
  have hw : width bits≤3*(bits.length+1) := by
    change max 1 bits.length+2≤3*(bits.length+1)
    omega
  have hc : limit bits≤6*(bits.length+1) := by
    change 3*(max 1 bits.length+1)≤6*(bits.length+1)
    omega
  have hwp : width bits+1≤4*(bits.length+1) := by omega
  have hp4 : (width bits+1)^4≤256*(bits.length+1)^4 := by
    calc
      _ ≤ (4*(bits.length+1))^4 := Nat.pow_le_pow_left hwp 4
      _ = _ := by ring
  have he : erase bits≤131072*(bits.length+1)^2 := by
    change 8192*(width bits+1)^2≤131072*(bits.length+1)^2
    nlinarith only [hwp]
  have hp2 : bits.length+1≤(bits.length+1)^2 := by nlinarith
  have hp24 : (bits.length+1)^2≤(bits.length+1)^4 := by
    have hpos : 1≤(bits.length+1)^2 := Nat.one_le_pow _ _ (by omega)
    calc
      _ = 1*(bits.length+1)^2 := by omega
      _ ≤ (bits.length+1)^2*(bits.length+1)^2 := Nat.mul_le_mul_right _ hpos
      _ = _ := by ring
  unfold budget bodyBudget RecoveryColdCompact.coldBudget RecoveryColdMarker.coldBudget
    RecoveryColdMarker.bankBudget RecoveryColdCompact.materializeBudget RecoveryColdCompact.bankBudget
    checkerBudget
  omega

theorem bounded_witness_budget (code : Nat) (word : List Bool)
    (hw : word.length≤128*(natBitLength code+1)^3) :
    budget code.bits word≤8796093022208*(natBitLength code+1)^4 := by
  have h := budget_bound code.bits word
  have hb := RecoveryUnpair.bits_length code
  have hp4 := Nat.pow_le_pow_left (Nat.add_le_add_right hb 1) 4
  have hp34 : (natBitLength code+1)^3≤(natBitLength code+1)^4 := by
    calc
      _ = 1*(natBitLength code+1)^3 := by omega
      _ ≤ (natBitLength code+1)*(natBitLength code+1)^3 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have hpos : 1≤(natBitLength code+1)^4 := Nat.one_le_pow _ _ (by omega)
  omega

end NearCubicWires.RepairOrdinary.RecoveryColdVerifier
