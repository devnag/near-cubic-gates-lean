import Proof.CaseAnalysis.CaseTwoSubstitutedCircuitEncoder
import Proof.MachineModel.RuntimeCaseTwoOccurrenceEncodingClosure

/-!
# The Case-2 encoder, reduced to the recovered oracle's own code

`RuntimeCaseTwoOccurrenceEncodingClosure` cut the bank/diagonal cluster down to
`InverseScheduledOccurrenceEncoding`: one fixed program emitting
`encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo)` from the public
length.  `CaseTwoSubstitutedCircuitEncoder` builds that encoder out of the
recovered oracle's *own* code together with three numerals that the bank
already emits — the native width, the scheduled source length and the refuter
word — so nothing of the substitution, the restriction or the arity padding is
left open.

§1 states the smaller premise: one program emitting the request word

> `pair (encodeBooleanCircuit caseTwo.circuit)
>   (pair nativeWidth (pair sourceLength (encodeBitInput refuterWord)))`

from the public length.  §2 links the substituted-circuit encoder onto it and
discharges `InverseScheduledOccurrenceEncoding` outright, so
`RuntimeCaseTwoOccurrenceEncodingClosure.inverse_clusterResiduals_ofEncoding`
applies with the assembler as the only constructive residue left in the bank
cluster.
-/

namespace NearCubicWires.RuntimeCaseTwoSubstitutedEncodingClosure

open NearCubicWires
open NearCubicWires.BankCaseTwoEnvelopeClosure
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoSubstitutedCircuitEncoder
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedOracleRestriction
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoOccurrenceEncodingClosure
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The request word -/

/-- **The Case-2 encoder's remaining premise.**  One fixed program that, from
the requested public length alone, emits the recovered oracle's own circuit
code beside the three numerals the substitution runner's request needs. -/
def InverseSubstitutionRequestWord
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (requestProgram : NPOracleProgram)
    (requestBits requestFuel : ℕ → ℕ) : Prop :=
  ∀ (target : ℕ)
    (_hlarge :
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target)
    (hyes :
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
        (sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target))
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target))
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
      (inverseRefuterInput contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target)),
    inverseTargetBranch contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target hyes = .caseTwo caseTwo →
    runNPOracleProgram requestProgram (requestBits target) (requestFuel target)
        (initialNPOracleState target target) =
      some
        (Nat.pair (encodeBooleanCircuit caseTwo.circuit)
          (Nat.pair
            ((publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
              (sourceLength
                (inverseChainSourceIndex contracts clockDepth advantageExponent
                  target)))
            (Nat.pair
              (sourceLength
                (inverseChainSourceIndex contracts clockDepth advantageExponent
                  target))
              (encodeBitInput
                (inverseRefuterInput contracts
                  (publishedHierarchyOuterPCP contracts clockDepth) machine
                  advantageExponent target)))))

/-! ## 2. The encoder from the request word -/

/-- The published encoder: the request word followed by the fixed
restrict/substitute/pad stream. -/
noncomputable def inverseSubstitutedEncodingProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (requestProgram : NPOracleProgram) : NPOracleProgram :=
  linkPrograms requestProgram
    (substitutedEncodingProgram
      (publishedHierarchyOuterPCP contracts clockDepth).substitution.runner.program)

/-- The published width envelope hypothesis the restriction stage consumes. -/
private theorem inverseNativeWidthLe
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) :
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
        (sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target)) ≤
      (paddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth)).nativeWidth
        (sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target)) :=
  nativeWidth_le_widthEnvelope (publishedHierarchyOuterPCP contracts clockDepth)
    (sourceLength
      (inverseChainSourceIndex contracts clockDepth advantageExponent target))

open Classical in
/-- The encoder's width at one target, quoted at the oracle the branch
carries. -/
noncomputable def inverseSubstitutedEncodingBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (requestBits : ℕ → ℕ) (target : ℕ) : ℕ :=
  if hyes :
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
        (sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target))
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target) then
    match
      inverseTargetBranch contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target hyes with
    | .caseOne _ => 0
    | .caseTwo caseTwo =>
        occurrenceStageBits target (requestBits target)
          (substitutedEncodingBits
            (publishedHierarchyOuterPCP contracts clockDepth).substitution
            target
            (inverseRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target)
            caseTwo.circuit
            (inverseNativeWidthLe contracts clockDepth advantageExponent
              target))
  else 0

open Classical in
/-- The encoder's clock at one target, a branch read for the same reason. -/
noncomputable def inverseSubstitutedEncodingFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (requestFuel : ℕ → ℕ) (target : ℕ) : ℕ :=
  if hyes :
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
        (sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target))
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target) then
    match
      inverseTargetBranch contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target hyes with
    | .caseOne _ => 0
    | .caseTwo caseTwo =>
        linkFuel
          (substitutedEncodingProgram
            (publishedHierarchyOuterPCP contracts
              clockDepth).substitution.runner.program)
          (requestFuel target)
          (substitutedEncodingFuel
            (publishedHierarchyOuterPCP contracts clockDepth).substitution
            target
            (inverseRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target)
            caseTwo.circuit
            (inverseNativeWidthLe contracts clockDepth advantageExponent
              target))
  else 0

set_option maxHeartbeats 400000 in
-- The statement carries the linked encoder and both branch envelopes at one
-- target, so elaborating it alone exceeds the default budget.
/-- **The Case-2 encoder, discharged from the request word.**  Restriction,
substitution and arity padding are all fixed programs, so the whole encoder
follows from one program emitting the recovered oracle's own code beside the
bank's three numerals. -/
theorem inverseScheduledOccurrenceEncoding_ofRequestWord
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (requestProgram : NPOracleProgram) (requestBits requestFuel : ℕ → ℕ)
    (hrequests :
      InverseSubstitutionRequestWord contracts clockDepth machine
        advantageExponent requestProgram requestBits requestFuel) :
    InverseScheduledOccurrenceEncoding contracts clockDepth machine
      advantageExponent
      (inverseSubstitutedEncodingProgram contracts clockDepth requestProgram)
      (inverseSubstitutedEncodingBits contracts clockDepth machine
        advantageExponent requestBits)
      (inverseSubstitutedEncodingFuel contracts clockDepth machine
        advantageExponent requestFuel) := by
  intro target hlarge hyes caseTwo hbranch
  have hrequest := hrequests target hlarge hyes caseTwo hbranch
  have hbits :
      inverseSubstitutedEncodingBits contracts clockDepth machine
          advantageExponent requestBits target =
        occurrenceStageBits target (requestBits target)
          (substitutedEncodingBits
            (publishedHierarchyOuterPCP contracts clockDepth).substitution
            target
            (inverseRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target)
            caseTwo.circuit
            (inverseNativeWidthLe contracts clockDepth advantageExponent
              target)) := by
    simp only [inverseSubstitutedEncodingBits]
    rw [dif_pos hyes, hbranch]
  have hfuel :
      inverseSubstitutedEncodingFuel contracts clockDepth machine
          advantageExponent requestFuel target =
        linkFuel
          (substitutedEncodingProgram
            (publishedHierarchyOuterPCP contracts
              clockDepth).substitution.runner.program)
          (requestFuel target)
          (substitutedEncodingFuel
            (publishedHierarchyOuterPCP contracts clockDepth).substitution
            target
            (inverseRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target)
            caseTwo.circuit
            (inverseNativeWidthLe contracts clockDepth advantageExponent
              target)) := by
    simp only [inverseSubstitutedEncodingFuel]
    rw [dif_pos hyes, hbranch]
  have htarget :
      encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo) =
        encodeBooleanCircuit
          ((publishedHierarchyOuterPCP contracts clockDepth).substitution.circuit
            (substRequest
              (inverseRefuterInput contracts
                (publishedHierarchyOuterPCP contracts clockDepth) machine
                advantageExponent target)
              caseTwo.circuit
              (inverseNativeWidthLe contracts clockDepth advantageExponent
                target))).padToArity :=
    rfl
  rw [hbits, hfuel, htarget, inverseSubstitutedEncodingProgram]
  exact run_occurrenceStage hrequest
    (run_substitutedEncodingProgram
      (publishedHierarchyOuterPCP contracts clockDepth).substitution target
      (inverseRefuterInput contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target)
      caseTwo.circuit
      (inverseNativeWidthLe contracts clockDepth advantageExponent target))

end NearCubicWires.RuntimeCaseTwoSubstitutedEncodingClosure
