import Proof.Assembly.PreparedSelected
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

open NativeRecipes

open SemanticRecipes
open RepairSource.SelectedRecoveryIntegration CloseoutWitness CanonicalWitnessCodec ProjectionNormalization

namespace AdmissionSourcePorts

/-- Original-family ports of the actual bounded admission, before body relocation. -/
noncomputable def familyPort (sources : EightSources) {gamma : Real}
    (p : Parameters sources gamma) (k : Nat) (mode : Bool) (i : Fin 3244) :
    Fin (WorkspaceSelectedAdmission.originalTapes sources p k) :=
  BoundedFamilySupport.slots (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
    k p.clauseDegree p.degree (WorkspaceSelectedAdmission.capacity sources p).E mode
    (ColdFamilySupport.familySlots (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
      k p.clauseDegree p.degree (BoundedFamily.exponent mode)
      (WorkspaceSelectedAdmission.capacity sources p).E i)

/-- The ready bank is an ambient bank: original tapes retain their actual indices. -/
noncomputable def readyPort (sources : EightSources) {gamma : Real}
    (p : Parameters sources gamma) (k r scratch : Nat) (mode : Bool) (i : Fin 3244) :
    Fin (SelectedBranchPhases.tapes sources p k r scratch) :=
  (((familyPort sources p k mode i).castAdd 1).castAdd 1).castAdd
    (ControllerSelectedContinuation.extra sources p k r scratch)

/-- Complete original-source boundary at the chosen, already executed ready bank.
The existential cursor describes the old retained-word theorem only. Current
physical heads are asserted separately. No decomposition-child cache is supplied. -/
noncomputable def ReadySources (sources : EightSources) {gamma : Real}
    (p : Parameters sources gamma) (den : Nat) (hden : 0 < den)
    (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) : Prop :=
  let source := fixedProjection sources
  let a := CloseoutLanguage.selectedPCPP sources
  let clock := PolynomialClock.ordinaryClock k
  let cap := WorkspaceSelectedAdmission.capacity sources p
  let H := SelectedSource.hierarchy sources k clock
  let Cpad := padding sources k clock
  let delta := CompetitorRationalGap.zeta (constantsOf sources)
  let mode := BoundedFields.symmetric bits
  let oracle := C10TotalDecode.oracleOf sources k clock p.degree n bits
  let bank := SelectedPhaseLayout.S.bank sources p den hden k r scratch n x bits hp
  let heads := SelectedPhaseLayout.S.heads sources p k r scratch
  SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp = mode ∧
  (∀ i : Fin 3244, heads (readyPort sources p k r scratch mode i) = 0) ∧
  (mode = true →
    SumFamily.decode symmetricCircuitCodec NormalizedSymmetricThresholdCircuit.wireCount
      NormalizedSymmetricThresholdCircuit.descriptionBits
      (P1Independent.CappedDecode.symLimits sources k clock p den x oracle)
      (CloseoutWitnessPolicy.variableCount sources k clock x oracle)
      (RadixSemantics.value (BoundedFields.family bits)) =
      some (P1Independent.CappedDecode.symFamilyOf sources k clock p den x oracle bits)) ∧
  (mode = false →
    SumFamily.decode thresholdCircuitCodec NormalizedThresholdThresholdCircuit.wireCount
      NormalizedThresholdThresholdCircuit.descriptionBits
      (P1Independent.CappedDecode.thrLimits sources k clock p den x oracle)
      (CloseoutWitnessPolicy.variableCount sources k clock x oracle)
      (RadixSemantics.value (BoundedFields.family bits)) =
      some (P1Independent.CappedDecode.thrFamilyOf sources k clock p den x oracle bits)) ∧
  ∃ decoded,
    decodeBooleanCircuit (SelectedOracle.width source k H.coefficient Cpad
      (SelectedSource.code sources k clock) (List.ofFn x))
      (RadixSemantics.value (BoundedFields.oracle bits)) = some decoded ∧
    decoded.size ≤ RecoveryScheduleEnvelope.oracleSizeBound p.degree
      (SelectedOracle.width source k H.coefficient Cpad
        (SelectedSource.code sources k clock) (List.ofFn x)) ∧
    HEq decoded oracle ∧
    let request := ColdNative.request source a k H.coefficient Cpad
      (SelectedSource.code sources k clock) x (Nat.le_max_right _ _) decoded
    let cb := (a.output request).clauseBits
    let W := LegalPolicy.W (BoundedFamily.exponent mode) den request.arity
    ∃ oldCursor : Fin 3244 → Nat,
      FamilySupport.retained mode (FamilyCapacity.value cap.E cap.K n)
        ((a.output request).systematicBits + (a.output request).auxiliaryBits)
        (FamilyResources.coefficientCap delta p.copies p.clauseDegree request.arity cb)
        (FamilyResources.termCap delta p.copies p.clauseDegree request.arity cb)
        request.arity W
        (DescriptionPolicy.value mode request.arity (CorePolicy.q0 p.clauseDegree request.arity) W)
        (CloseoutMassThreshold.literalWidth delta p.copies)
        (CloseoutSampledWitness.massCap delta p.copies) (BoundedFields.family bits) []
        oldCursor (fun i => bank (readyPort sources p k r scratch mode i))

noncomputable abbrev Certificate : Prop :=
  ∀ (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true),
    ReadySources sources p den hden k r scratch n x bits hp

end AdmissionSourcePorts
