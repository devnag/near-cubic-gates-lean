import Proof.MachineModel.CanonicalTargetLanguageProgram

/-!
# The Case-2 seed bit as three factory-runner calls

`CanonicalTargetLanguageProgram.caseTwoSeed_apply` reduces one scheduled
Case-2 seed bit to one padded honest-occurrence value of the published PCPP
factory.  This module removes the last semantic wrapper from that value: the
`SourceHonestPCPPTable`, the choice hidden in `caseTwoTable`, and both padding
layers disappear, leaving exactly

* one `clauseRunner` call selecting the requested two-literal clause,
* one `supportRunner` call per systematic coordinate, folded by `parityOn`,
* one `honestRunner` call supplying the auxiliary block.

`caseTwoSeed_apply_executable` is therefore the precise contract that the
executable Case-2 occurrence evaluator has to meet: its right-hand side
mentions only `ExecutablePointwisePCPP` runner executions and one parity fold
over already decoded data.
-/

namespace NearCubicWires.CaseTwoOccurrenceSpecification

open NearCubicWires
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces

/-! ## 1. One occurrence value of an executable pointwise PCPP -/

/-- The literal selected by one occurrence coordinate.  Reading it costs
exactly one `clauseRunner` execution. -/
noncomputable def executableOccurrenceLiteral
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : ExecutablePointwisePCPP circuit)
    (encoded : BitInput (n + pcpp.clauseBits + 1)) :
    Literal (pcpp.systematicBits + pcpp.auxiliaryBits) :=
  if occurrencePosition encoded then
    (pcpp.clause (binaryAddress (occurrenceClauseAddress encoded))).right
  else
    (pcpp.clause (binaryAddress (occurrenceClauseAddress encoded))).left

/-- The honest assignment read by the same coordinate: a parity fold over one
`supportRunner` execution on the systematic block, and one `honestRunner`
execution on the auxiliary block. -/
noncomputable def executableOccurrenceAssignment
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : ExecutablePointwisePCPP circuit) (input : BitInput n) :
    BitInput (pcpp.systematicBits + pcpp.auxiliaryBits) :=
  Fin.addCases (fun i => parityOn (pcpp.systematicSupport i) input)
    (pcpp.honestAuxiliary input)

/-- One honest occurrence bit of the executable factory instantiation. -/
noncomputable def executableOccurrenceValue
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : ExecutablePointwisePCPP circuit)
    (encoded : BitInput (n + pcpp.clauseBits + 1)) : Bool :=
  (executableOccurrenceLiteral pcpp encoded).eval
    (executableOccurrenceAssignment pcpp (occurrenceInput encoded))

/-- The semantic honest occurrence function of an executable pointwise PCPP is
literally the runner composition above. -/
theorem honestOccurrenceFunction_toSemantic
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : ExecutablePointwisePCPP circuit)
    (supportBound : ∀ i, (pcpp.systematicSupport i).card ≤ n / 2)
    (encoded : BitInput (n + pcpp.clauseBits + 1)) :
    honestOccurrenceFunction (pcpp.toSemantic supportBound) encoded =
      executableOccurrenceValue pcpp encoded :=
  rfl

/-! ## 2. The scheduled Case-2 instance -/

/-- The published factory instantiated once on the Case-2 substituted
circuit.  This is the only executable object the Case-2 evaluator consumes. -/
def caseTwoFactoryPCPP
    (pcppSource : UniformPointwisePCPPSource)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input) :
    ExecutablePointwisePCPP (caseTwoSubstitutedCircuit caseTwo) :=
  pcppSource.factory.forCircuit (caseTwoSubstitutedCircuit caseTwo)

/-- The factory's own clause width is below the scheduled clause envelope. -/
theorem caseTwoFactoryPCPP_clauseBits_le
    (pcppSource : UniformPointwisePCPPSource)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input) :
    (caseTwoFactoryPCPP pcppSource caseTwo).clauseBits ≤
      clauseBitsEnvelope outer pcppSource (oracleSizeBound requiredDegree)
        (sourceLength sourceIndex) :=
  (caseTwoFactoryTable pcppSource caseTwo).clauseBits_le_envelope_of_paddedOracle
    outer pcppSource (oracleSizeBound requiredDegree) input caseTwo.circuit
    caseTwo.sizeBounded

/-- The exact occurrence coordinate the factory is asked about: drop the two
scheduled padding axes from the requested seed point. -/
noncomputable def caseTwoOccurrenceCoordinates
    (pcppSource : UniformPointwisePCPPSource)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input)
    (point :
      BitInput (seedArity outer pcppSource requiredDegree sourceIndex)) :
    BitInput
      (outer.pcp.nativeWidth (sourceLength sourceIndex) +
        (caseTwoFactoryPCPP pcppSource caseTwo).clauseBits + 1) :=
  projectPaddedOccurrenceInput
    (caseTwoFactoryPCPP_clauseBits_le pcppSource caseTwo)
    (projectPaddedSystematicOccurrenceInput
      (nativeWidth_le_widthEnvelope outer (sourceLength sourceIndex))
      (fun index =>
        point
          (Fin.cast
            (seedArity_eq_envelope outer pcppSource requiredDegree
              sourceIndex).symm index)))

/-- Exact executable specification of one Case-2 seed bit.  The right-hand
side contains no choice, no `SourceHonestPCPPTable`, and no semantic PCPP: it
is one clause-runner call, one honest-runner call, and one parity fold over
support-runner calls, all on the published factory's instantiation of the
substituted circuit recovered by the bounded-oracle description bit. -/
theorem caseTwoSeed_apply_executable
    (pcppSource : UniformPointwisePCPPSource)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input)
    (point :
      BitInput (seedArity outer pcppSource requiredDegree sourceIndex)) :
    caseTwoSeed pcppSource caseTwo point =
      executableOccurrenceValue (caseTwoFactoryPCPP pcppSource caseTwo)
        (caseTwoOccurrenceCoordinates pcppSource caseTwo point) := by
  rw [caseTwoSeed_apply pcppSource caseTwo point]
  unfold SourceHonestPCPPTable.paddedFunction
  rw [fullyPaddedHonestOccurrenceFunction_eq]
  rfl

end NearCubicWires.CaseTwoOccurrenceSpecification
