import Proof.Foundations.ScheduledRecovery

/-!
# Determinacy of the Case-2 seed

`caseTwoTable` selects a `SourceHonestPCPPTable` with choice, but every such
table pins its executable component to the one factory chosen before any
oracle, and its support bound is propositional.  The semantic table, the
padded occurrence function, and the scheduled Case-2 seed are therefore
independent of the selection.  An executable layer may construct any concrete
table and identify its output with the scheduled seed through these lemmas;
no second seed definition and no new choice is introduced.
-/

namespace NearCubicWires.CaseTwoSeedDeterminacy

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedOracleRestriction
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery

/-- Any two source-honest tables over one circuit share one semantic view:
their executables are both the factory instantiation, and the support bound
is proof-irrelevant. -/
theorem sourceHonestPCPPTable_semantic_eq
    (pcppSource : UniformPointwisePCPPSource)
    {n : ℕ} {circuit : BooleanCircuit n}
    (left right : SourceHonestPCPPTable pcppSource circuit) :
    left.table.semantic = right.table.semantic := by
  have hexecutable :
      left.table.executable = right.table.executable :=
    left.executable_eq.trans right.executable_eq.symm
  unfold HonestPCPPTable.semantic
  congr 1

/-- The padded honest occurrence function is table-independent. -/
theorem sourceHonestPCPPTable_paddedFunction_eq
    {depth : ℕ}
    {source : ExecutableRefuterSource (pairClock depth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (oracleSizeBound : ℕ → ℕ) {n : ℕ} (input : BitInput n)
    (oracle : BooleanCircuit (widthEnvelope outer n))
    (horacle :
      oracle.size ≤ oracleSizeBound (widthEnvelope outer n))
    (left right : SourceHonestPCPPTable pcppSource
      (outer.pcppCircuit input
        (restrictPaddedOracle oracle
          (nativeWidth_le_widthEnvelope outer n)))) :
    left.paddedFunction outer pcppSource oracleSizeBound input oracle
        horacle =
      right.paddedFunction outer pcppSource oracleSizeBound input oracle
        horacle := by
  unfold SourceHonestPCPPTable.paddedFunction
  congr 1
  exact sourceHonestPCPPTable_semantic_eq pcppSource left right

/-- The scheduled Case-2 seed computed from one explicitly supplied table,
through exactly the arity identification used by `caseTwoSeed`. -/
noncomputable def seedOfTable
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    (pcppSource : UniformPointwisePCPPSource)
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input)
    (table : SourceHonestPCPPTable pcppSource
      (outer.pcppCircuit input
        (restrictPaddedOracle caseTwo.circuit
          (nativeWidth_le_widthEnvelope outer
            (sourceLength sourceIndex))))) :
    BoolFunction
      (seedArity outer pcppSource requiredDegree sourceIndex) := by
  simpa only [seedArity, scheduledWidth,
    scheduledClauseBits_eq_envelope] using
    table.paddedFunction outer pcppSource (oracleSizeBound requiredDegree)
      input caseTwo.circuit caseTwo.sizeBounded

/-- The choice inside `caseTwoTable` is invisible: the scheduled seed equals
the seed computed from any concretely constructed table. -/
theorem caseTwoSeed_eq_seedOfTable
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    (pcppSource : UniformPointwisePCPPSource)
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input)
    (table : SourceHonestPCPPTable pcppSource
      (outer.pcppCircuit input
        (restrictPaddedOracle caseTwo.circuit
          (nativeWidth_le_widthEnvelope outer
            (sourceLength sourceIndex))))) :
    caseTwoSeed pcppSource caseTwo =
      seedOfTable pcppSource caseTwo table := by
  unfold caseTwoSeed seedOfTable
  congr 1
  exact sourceHonestPCPPTable_paddedFunction_eq outer pcppSource
    (oracleSizeBound requiredDegree) input caseTwo.circuit
    caseTwo.sizeBounded (caseTwoTable pcppSource caseTwo) table

end NearCubicWires.CaseTwoSeedDeterminacy
