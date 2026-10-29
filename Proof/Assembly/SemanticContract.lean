import Proof.Assembly.NativeNativeSelected
import Proof.CaseAnalysis.FinalModeNativeStageFields
import Proof.CaseAnalysis.FinalSupplierAccuracyChain

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

open NativeRecipes

namespace SemanticRecipes

open CloseoutFinalC10ModeNativeStageFields
open CloseoutFinalC10SupplierCalls
open C10SupplierAccuracyChain

noncomputable abbrev supplier (sources : EightSources) (liveScale target : Nat)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (mode : Bool) (atoms : List (C10TotalDecode.Atom pcpp)) : Rat :=
  ((modeEstimate sources liveScale target mode atoms).num : Rat) /
    (modeEstimate sources liveScale target mode atoms).den

noncomputable abbrev failure (target : Nat) : Real := 1 / (target + 1 : Nat)

/-- A semantic certificate only for the actual records, with all bounds explicit. -/
noncomputable abbrev Certificate : Prop :=
  ∀ (sources : EightSources) (liveScale target : Nat)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (mode : Bool) (ph : Phase)
    (P : CircuitPolynomial (C10TotalDecode.Atom pcpp) 4)
    (b denBits : Nat) (limits : CanonicalWitnessCodec.LegalSumLimits)
    (order : List (CircuitMonomial (C10TotalDecode.Atom pcpp) 4))
    (entries : List Stream.Entry),
    P.monomials.Perm order →
    List.Forall₂ (fun m e =>
      e.coefficient = coefficientEstimate m.coefficient ∧
      e.count = (modeEstimate sources liveScale target mode m.factors).num ∧
      e.denominator = (modeEstimate sources liveScale target mode m.factors).den)
      order entries →
    (P.coefficientMass : Rat) ≤ C10FamilyMass.siteMassBound limits.coefficientMassCap ph →
    CoefficientsFit b P →
    accuracyTarget (constantsOf sources) limits ph ≤ target →
    0 < target →
    (∀ m ∈ order, (modeEstimate sources liveScale target mode m.factors).den ≤ 2^denBits) →
    denBits + 1 ≤ b →
    0 ≤ failure target ∧
    (∀ m ∈ P.monomials,
      |((supplier sources liveScale target mode m.factors : Rat) : Real) -
        SupplierPipeline.conjunctionProbability C10TotalDecode.evaluate m.factors| ≤ failure target) ∧
    failure target * ((P.coefficientMass : Rat) : Real) ≤
      ((CompetitorRationalGap.estimationTolerance (constantsOf sources)
        (CompetitorRationalGap.zeta (constantsOf sources)) : Rat) : Real) ∧
    OrderedCallPhases.OrderedCalls (supplier sources liveScale target mode) P.monomials entries ∧
    (∀ e ∈ entries, Stream.Entry.Valid b e)

end SemanticRecipes
