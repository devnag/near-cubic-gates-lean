import Proof.CaseAnalysis.WitnessBoundedFamilyPreHierarchy
import Proof.PCP.VerifierDecodingFields

/-! The honest canonical family becomes an exact N/16-bit ordinary guess.
The existing bounded header sees the same mode, oracle and family payload. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFields
open SourceInterfaces RepairSource CanonicalWitnessCodec CanonicalRecoveryLanguage
open RadixSemantics SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem encoded_guess {limits : RecoveryWitnessLimits}
    {count : BooleanCircuit limits.oracleArity→ℕ} (w : FamilyWitness limits count) (N : ℕ)
    (hcode:natBitLength w.code≤N/16) :
    ∃ guess : BitInput (N/16),
      value (List.ofFn guess)=w.code ∧
      16*(List.ofFn guess).length≤N ∧
      CompetitorWitnessTriple.headerValid (List.ofFn guess) ∧
      decodeBooleanCircuit limits.oracleArity (value (oracle (List.ofFn guess)))=some w.oracle ∧
      value (family (List.ofFn guess))=w.payload ∧
      symmetric (List.ofFn guess)=decide (w.mode=0) := by
  let guess:=bitInputOfCode (N/16) w.code
  have word:List.ofFn guess=binary (N/16) w.code:=VerifierDecoding.fixedBits_binary _ _
  have small:w.code<2^(N/16):=
    (Nat.lt_pow_succ_log_self (by decide : 1<2) w.code).trans_le
      (Nat.pow_le_pow_right (by decide : 0<2) hcode)
  have hv:value (List.ofFn guess)=w.code:=by rw [word];exact binary_value _ _ small
  obtain ⟨header,horacle,hfamily⟩:=w.header_fields _ hv
  obtain ⟨_struct,hmode,_oracle,_family⟩:=CompetitorWitnessTriple.extracted_values
    (List.ofFn guess) _ _ _ hv
  refine ⟨guess,hv,?_,header,?_,hfamily,?_⟩
  · rw [List.length_ofFn]
    exact Nat.mul_div_le N 16
  · change decodeBooleanCircuit limits.oracleArity (CompetitorWitnessTriple.field (List.ofFn guess) 3)=_
    rw [horacle]
    exact decodeBooleanCircuit_encode w.oracle
  · unfold symmetric
    rw [hmode]
    cases w <;> simp only [FamilyWitness.mode,CompetitorWitnessTriple.encoded_modes.1,
      CompetitorWitnessTriple.encoded_modes.2]
    norm_num

end NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFields
