import Proof.Assembly.Selected
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

open NativeRecipes

namespace FixedLivePackets

theorem parent (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws) (tables : TableCertificate) (semantics : Certificate) (physical : PreparedRecipe selector compiler tables semantics) : Target := by
 classical
 intro buildSource
 have chosen := physical buildSource
 rcases chosen with ⟨capIndex,remainingDegree,r,base,scratch,site,remainingFuel,widths,phaseConstruction,remainingCoefficient,remainingOnset,tableCoefficient,tableDegree,runtimeBound⟩
 refine ⟨capIndex,remainingDegree,r,base,scratch,site,remainingFuel,widths,?_,remainingCoefficient,remainingOnset,tableCoefficient,tableDegree,runtimeBound⟩
 intro sources gamma hg hh p n x bits C hn hp
 exact selectedProjection selector compiler tables semantics buildSource sources p
  (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p))
  C.k (r sources gamma hg hh p) (scratch sources gamma hg hh p) n x bits hp
  (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p n)
  (widths sources gamma hg hh p n x bits) (phaseConstruction sources gamma hg hh p n x bits hn hp)

end FixedLivePackets
