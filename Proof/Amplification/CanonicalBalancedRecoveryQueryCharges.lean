import Proof.Circuits.TotalInverseCanonicalBodySelectorLocalClosure
import Proof.MachineModel.BalancedRecoveryQuerySelectorProgram

namespace NearCubicWires.CanonicalBalancedRecoveryQueryCharges

open NearCubicWires
open NearCubicWires.BalancedCNFSATEncoding
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BalancedCNFSATEncodingConservativeExtension
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CircuitInputCNF
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.TotalInverseCanonicalBodySelectorLocalClosure
open NearCubicWires.TseitinCNF
open NearCubicWires.UniformTargetLanguageBank

private abbrev Request := LanguageEvaluationRequest

/-! ## 1. The canonical schedule objects, named once -/

/-- The canonical structural atom schedule at the recovery coordinates —
the list every recovery-query charge runs over. -/
noncomputable def canonicalBodyAtomSchedule
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (request : Request) : List ℕ :=
  boundedOracleStructuralFormulaAtoms
    (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
    (inverseRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      advantageExponent request.length)
    (inverseScheduleBound contracts clockDepth advantageExponent
      request.length)

/-- The canonical recovery formula at the recovery coordinates. -/
noncomputable def canonicalRecoveryFormula
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (request : Request) : EncodedCNF :=
  boundedOracleRecoveryFormula
    (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
    (inverseRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      advantageExponent request.length)
    (inverseScheduleBound contracts clockDepth advantageExponent
      request.length)

/-- Coordinate witness: the frozen tagged atom code is `encodeTaggedList` of
exactly this schedule. -/
theorem canonicalBodyAtomCode_eq_taggedSchedule
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (request : Request) :
    canonicalBodyAtomCode contracts clockDepth machine advantageExponent
        request =
      encodeTaggedList
        (canonicalBodyAtomSchedule contracts clockDepth machine
          advantageExponent request) :=
  rfl

/-- Coordinate witness: the frozen recovery code is the standard `Encodable`
code of exactly this formula. -/
theorem canonicalBodyRecoveryCode_eq_encodeFormula
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (request : Request) :
    canonicalBodyRecoveryCode contracts clockDepth machine advantageExponent
        request =
      Encodable.encode
        (canonicalRecoveryFormula contracts clockDepth machine
          advantageExponent request) :=
  rfl

/-! ## 2. The balanced twins -/

noncomputable def canonicalBodyAtomCodeBalanced
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (request : Request) : ℕ :=
  encodeBalancedList
    (canonicalBodyAtomSchedule contracts clockDepth machine advantageExponent
      request)

/-- **The clause stream at `encodeBalancedList`**: the balanced list of the
canonical clause codes of the recovery formula. -/
noncomputable def canonicalRecoveryBalancedPayload
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (request : Request) : ℕ :=
  balancedCNFPayload
    (canonicalRecoveryFormula contracts clockDepth machine advantageExponent
      request)

/-- **The balanced query word**: the flat compact marker around the balanced
clause payload — the word the balanced branch query submits to `.sat`. -/
noncomputable def canonicalRecoveryBalancedQueryWord
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (request : Request) : ℕ :=
  encodeBalancedCNF
    (canonicalRecoveryFormula contracts clockDepth machine advantageExponent
      request)

/-! ## 3. Width ledgers — polynomial in the schedule's own list data -/

/-- The balanced atom code is polynomial in the atom count and the atom
widths (`balancedListCodeBits_le` at the canonical schedule).  The frozen
twin at the same coordinate pays `2 ^ Θ(atoms.length)`
(`two_pow_sq_le_natBitLength_canonicalBodyAtomCode`). -/
theorem natBitLength_canonicalBodyAtomCodeBalanced_le
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (request : Request) :
    natBitLength
        (canonicalBodyAtomCodeBalanced contracts clockDepth machine
          advantageExponent request) ≤
      1 +
        2 *
          (canonicalBodyAtomSchedule contracts clockDepth machine
            advantageExponent request).length ^ 4 *
          balancedListAtomBits
            (canonicalBodyAtomSchedule contracts clockDepth machine
              advantageExponent request) :=
  balancedListCodeBits_le
    (canonicalBodyAtomSchedule contracts clockDepth machine advantageExponent
      request)

/-- The balanced clause payload is polynomial in the clause count and the
clause-code widths. -/
theorem natBitLength_canonicalRecoveryBalancedPayload_le
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (request : Request) :
    natBitLength
        (canonicalRecoveryBalancedPayload contracts clockDepth machine
          advantageExponent request) ≤
      1 +
        2 *
          (canonicalRecoveryFormula contracts clockDepth machine
            advantageExponent request).length ^ 4 *
          balancedListAtomBits
            ((canonicalRecoveryFormula contracts clockDepth machine
              advantageExponent request).map Encodable.encode) := by
  have hbound := balancedListCodeBits_le
    ((canonicalRecoveryFormula contracts clockDepth machine advantageExponent
      request).map Encodable.encode)
  simpa only [canonicalRecoveryBalancedPayload, balancedCNFPayload,
    List.length_map] using hbound

/-- The balanced query word keeps the payload's polynomial width under a
constant-depth marker (`encodeBalancedCNF_bits_le_clauseAtoms` at the
canonical formula).  The frozen recovery code at the same coordinate is
geometric in the clause count
(`two_pow_pred_length_le_natBitLength_encode_circuitInputFormula`). -/
theorem natBitLength_canonicalRecoveryBalancedQueryWord_le
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (request : Request) :
    natBitLength
        (canonicalRecoveryBalancedQueryWord contracts clockDepth machine
          advantageExponent request) ≤
      16 *
          max 1
            (1 +
              2 *
                (canonicalRecoveryFormula contracts clockDepth machine
                  advantageExponent request).length ^ 4 *
                balancedListAtomBits
                  ((canonicalRecoveryFormula contracts clockDepth machine
                    advantageExponent request).map Encodable.encode)) +
        7 :=
  encodeBalancedCNF_bits_le_clauseAtoms
    (canonicalRecoveryFormula contracts clockDepth machine advantageExponent
      request)

/-! ## 4. The branch decision at the balanced word, canonical coordinate -/

/-- The balanced query word decides exactly the frozen recovery code's
branch: the flat conservative extension meets the recovery formula's
well-sizedness at the canonical coordinate. -/
theorem encodedSat_canonicalRecoveryBalancedQueryWord
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (request : Request) :
    encodedSat
        (canonicalRecoveryBalancedQueryWord contracts clockDepth machine
          advantageExponent request) =
      encodedSat
        (canonicalBodyRecoveryCode contracts clockDepth machine
          advantageExponent request) := by
  have hleft := encodedSat_encodeBalancedCNF
    (canonicalRecoveryFormula contracts clockDepth machine advantageExponent
      request)
  have hwell :
      wellSizedCNFEncoding
          (canonicalBodyRecoveryCode contracts clockDepth machine
            advantageExponent request)
          (decodeCNF
            (canonicalBodyRecoveryCode contracts clockDepth machine
              advantageExponent request)) = true := by
    have hformula := boundedOracleRecoveryFormula_wellSized
      (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
      (inverseRefuterInput contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent request.length)
      (inverseScheduleBound contracts clockDepth advantageExponent
        request.length)
    simpa only [canonicalBodyRecoveryCode, boundedOracleRecoveryCode,
      decodeCNF_encode] using hformula
  have hright := encodedSat_eq_legacyEncodedSat_of_wellSized hwell
  rw [canonicalRecoveryBalancedQueryWord, hleft, hright]
  rfl

end NearCubicWires.CanonicalBalancedRecoveryQueryCharges
