import Lean
import Proof.Amplification.CaseOneRecoveryAssembly
import Proof.Amplification.RecoveryCaseOneBooleanOutput
import Proof.Amplification.RecoveryCaseOnePaddedBitInput
import Proof.Amplification.RecoveryCaseOnePaddedOrdinaryRun
import Proof.Amplification.RecoveryCaseOneRequest
import Proof.Amplification.RecoveryEncodedNPVerifier
import Proof.Amplification.RecoveryFocusRetained
import Proof.Amplification.RecoveryPCPFormulaResumeHierarchyActual
import Proof.Amplification.RecoveryPCPFormulaResumeSearchCountFrame
import Proof.Amplification.RecoveryPrefixLoopDock
import Proof.Amplification.RecoveryPrefixPrepareCall
import Proof.Amplification.RecoveryRefuterReplayWhole
import Proof.Amplification.RecoveryScratchErase
import Proof.Amplification.RecoveryTseitinRawIncrement
import Proof.Amplification.RecoveryTseitinReadOnly
import Proof.Amplification.XorResourcesProjection
import Proof.Assembly.AppendOutputFrame
import Proof.Assembly.AppendOutputLength
import Proof.CaseAnalysis.CapacityBudget
import Proof.CaseAnalysis.CapacityPower
import Proof.CaseAnalysis.CaseOneDirect
import Proof.CaseAnalysis.CaseOneDirectBound
import Proof.CaseAnalysis.CaseTwoBlockScalars
import Proof.CaseAnalysis.CaseTwoHierarchyFrame
import Proof.CaseAnalysis.CaseTwoHonestInput
import Proof.CaseAnalysis.CaseTwoLoad
import Proof.CaseAnalysis.CaseTwoLogs
import Proof.CaseAnalysis.CaseTwoMetadata
import Proof.CaseAnalysis.CaseTwoNativeHeaderJoin
import Proof.CaseAnalysis.CaseTwoOccurrenceBitRun
import Proof.CaseAnalysis.CaseTwoSourceBlockPorts
import Proof.CaseAnalysis.CaseTwoWholeBudgetHierarchy
import Proof.CaseAnalysis.ClauseWidth
import Proof.CaseAnalysis.CommonPortBank
import Proof.CaseAnalysis.CommonPortBankAt
import Proof.CaseAnalysis.CommonPrepareBudget
import Proof.CaseAnalysis.CommonPrepareLayout
import Proof.CaseAnalysis.CommonQueryClear
import Proof.CaseAnalysis.FamilyCodeEnvelope
import Proof.CaseAnalysis.NativeWidthStep
import Proof.CaseAnalysis.Parameters
import Proof.CaseAnalysis.RawRowsPaperCaps
import Proof.CaseAnalysis.RecoveryCapacityDriversPowers
import Proof.CaseAnalysis.RecoveryFullBoundResources
import Proof.CaseAnalysis.RecoveryGraphOriginal
import Proof.CaseAnalysis.RecoveryHierarchyDockCount
import Proof.CaseAnalysis.RecoveryPreparedLayout
import Proof.CaseAnalysis.RecoveryProjectionBudget
import Proof.CaseAnalysis.RecoverySearchGraphBudget
import Proof.CaseAnalysis.RecoverySearchJoin
import Proof.CaseAnalysis.RecoverySourceIdentity
import Proof.CaseAnalysis.RecoveryWorkspacePolynomial
import Proof.CaseAnalysis.RetainedRefuterRun
import Proof.CaseAnalysis.RowsCircuitHeader
import Proof.CaseAnalysis.RowsGateSourceRun
import Proof.CaseAnalysis.RowsMetadataCopy
import Proof.CaseAnalysis.ScheduleClog
import Proof.CaseAnalysis.ScheduleCompare
import Proof.CaseAnalysis.ScheduleOnsetGuard
import Proof.CaseAnalysis.ScheduleScale
import Proof.CaseAnalysis.ScheduleSourceWord
import Proof.CaseAnalysis.SourceCounts
import Proof.CaseAnalysis.SourceTermMeaning
import Proof.CaseAnalysis.WitnessAliases
import Proof.CaseAnalysis.WitnessHonest
import Proof.CaseAnalysis.Xor
import Proof.Circuits.DecompositionCountDrivers
import Proof.Circuits.MatrixBucketDimensionsIncrement
import Proof.Circuits.PaddedRunnerBudgetClosure
import Proof.Foundations.PolynomialSchedule
import Proof.Foundations.SourceRegistry
import Proof.Foundations.WireScaleTransfer
import Proof.Hierarchy.HierarchyAllocation
import Proof.Hierarchy.HierarchyFixedWord
import Proof.Hierarchy.HierarchyNormalizedRealization
import Proof.Hierarchy.HierarchyProjectionPrefix
import Proof.Hierarchy.HierarchyStreamReady
import Proof.MachineModel.ClockUnarySum
import Proof.MachineModel.GeneratedAmplifierSemantics
import Proof.MachineModel.OrdinaryMaskedReset
import Proof.MachineModel.OrdinaryMatrixUnaryTemplate
import Proof.MachineModel.OrdinaryOracleCompose
import Proof.MachineModel.OrdinaryOracleComposeInitial
import Proof.MachineModel.OrdinaryOracleComposeReadyAt
import Proof.MachineModel.OrdinaryRewindWorkspace
import Proof.PCP.PCPPNativeCanonicalBounds
import Proof.PCP.PCPPNativeCanonicalTreeWeight
import Proof.PCP.PCPPNativeForwardScalar
import Proof.PCP.PCPPNativeHierarchyNodesCircuit
import Proof.PCP.PCPPNativeNaturalAppend
import Proof.PCP.PCPPQueryField
import Proof.PCP.PCPPRequestNodeSchema
import Proof.PCP.PCPPairReusable
import Proof.PCP.PCPSerializerCapacityFocus
import Proof.PCP.PCPSerializerTapeSupport
import Proof.PCP.ProjectionDimensionPolynomialBounds
import Proof.PCP.VerifierDecodingRepeat
import Proof.PCP.VerifierDecodingSlice

set_option autoImplicit false

namespace NearCubicGates.Close.GateRecoveryAlias

open Lean Elab Command

/-- Add `GR.NearCubicWires.x ↦ NearCubicWires.x` for every non-internal base declaration and register the
mirrored namespaces. -/
def aliasBase : CommandElabM Unit := do
  let env ← getEnv
  let root := `NearCubicWires
  let mut out := env
  for (n, _) in env.constants.map₁.toList do
    if root.isPrefixOf n && !n.isInternal then
      out := Lean.addAlias out (`GR ++ n) n
  for ns in env.getNamespaces.toList do
    if root.isPrefixOf ns then
      out := out.registerNamespace (`GR ++ ns)
  setEnv out

/-- See `aliasBase`. -/
elab "gr_alias_base" : command => aliasBase

end NearCubicGates.Close.GateRecoveryAlias

run_cmd NearCubicGates.Close.GateRecoveryAlias.aliasBase
