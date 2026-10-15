import Proof.Amplification.RecoveryCompactSize
import Proof.Foundations.RecoveryOracleContracts

/-! Immediate ordinary-NP consumer of the compact semantic/size parent.
`realizes` below is the remaining LOCAL machine theorem: it must be proved
for one actual finite ordinary verifier, with the displayed polynomial clock.
This module provides no postulate or instance claiming that implementation exists. -/
namespace NearCubicWires.RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem compact_witness_envelope (code coefficient degree : Nat)
    (hc : 3 ≤ coefficient) (hd : 1 ≤ degree) :
    3 * natBitLength code ≤ coefficient * (natBitLength code + 1) ^ degree := by
  have hp : natBitLength code + 1 ≤ (natBitLength code + 1) ^ degree := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < natBitLength code + 1) hd
  exact Nat.mul_le_mul hc ((by omega : natBitLength code ≤ natBitLength code + 1).trans hp)

/-- The exact remaining deterministic checker implementation boundary. It
handles every code and every witness in the same polynomial envelope used
by EncodedNPVerifier.correct; oversized assignment witnesses must be rejected
by the actual finite machine just as by correctedWitnessVerifier. -/
def encodedNPVerifierOfCompactRealization
    (verifier : OrdinaryVerifier) (coefficient degree : Nat)
    (hc : 3 ≤ coefficient) (hd : 1 ≤ degree)
    (realizes : ∀ (code : Nat) (witness : List Bool),
      witness.length ≤ coefficient * (natBitLength code + 1) ^ degree →
      (verifier.acceptsAt (coefficient * (natBitLength code + 1) ^ degree)
        code.bits witness ↔ correctedWitnessVerifier code witness = true)) :
    EncodedNPVerifier correctedSat where
  verifier := verifier
  coefficient := coefficient
  coefficientPositive := by omega
  degree := degree
  correct := by
    intro code
    rw [correctedSat_bounded_witness]
    constructor
    · rintro ⟨witness, hlength, hcheck⟩
      have hpoly := hlength.trans (compact_witness_envelope code coefficient degree hc hd)
      exact ⟨witness, hpoly, (realizes code witness hpoly).mpr hcheck⟩
    · rintro ⟨witness, hpoly, haccept⟩
      have hcheck := (realizes code witness hpoly).mp haccept
      exact ⟨witness, corrected_witness_length hcheck, hcheck⟩

end NearCubicWires.RepairSource.RecoveryOracle
