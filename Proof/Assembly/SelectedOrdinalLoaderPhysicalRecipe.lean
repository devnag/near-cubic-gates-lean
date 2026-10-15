import Proof.Assembly.PhaseOrdinalLoaderPhysicalRecipe
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

open NativeRecipes
open SemanticRecipes

namespace FetchRecipes

noncomputable abbrev FetchSelected (fetchCorrect : IndexFetchProgram.Correct) (semantics : Certificate) (buildSource : SourceBuilder) (sourceProjection : SourceProjection) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (den : Nat) (hden : 0<den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
 (hp : P1Independent.CappedLegalAdmission.passed sources p
  (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
  (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
 (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (remainingFuel : Nat) (width : Phase → Nat) : Prop :=
∃ (cost : Phase → Nat),
∃ (penaltySpec : FetchPhase sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .penalty (SelectedPhaseLayout.S.heads sources p k r scratch) (SelectedPhaseLayout.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty)),
let penalty := (fetchBuildPhase fetchCorrect semantics buildSource sourceProjection) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .penalty (SelectedPhaseLayout.S.heads sources p k r scratch) (SelectedPhaseLayout.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) penaltySpec
∃ (momentSpec : FetchPhase sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .moment penalty.realize.heads penalty.realize.exit (cost .moment) (width .moment)),
let moment := (fetchBuildPhase fetchCorrect semantics buildSource sourceProjection) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .moment penalty.realize.heads penalty.realize.exit (cost .moment) (width .moment) momentSpec
∃ (clauseSpec : FetchPhase sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .clause moment.realize.heads moment.realize.exit (cost .clause) (width .clause)),
let clause := (fetchBuildPhase fetchCorrect semantics buildSource sourceProjection) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .clause moment.realize.heads moment.realize.exit (cost .clause) (width .clause) clauseSpec
∃ (_penalty_kept : clause.realize.exit (SelectedPhaseLayout.S.ports sources p k r scratch .penalty)=
   CloseoutRowsEstimatorCoefficients.Stream.recordWord (width .penalty) penalty.realize.result 1 1),
∃ (_moment_kept : clause.realize.exit (SelectedPhaseLayout.S.ports sources p k r scratch .moment)=
   CloseoutRowsEstimatorCoefficients.Stream.recordWord (width .moment) moment.realize.result 1 1),
∃ (_threshold : ∀ ph,C10ThresholdWidths.thresholdWidth (constantsOf sources)≤width ph),
∃ (_head : ∀ i,clause.realize.heads (SelectedBranchPhases.body sources p k r scratch
   (CloseoutFinalC10RetainedPhaseFold.tailSlots (SelectedBranchPhases.offset sources p k r)
    (ControllerSelectedContinuation.bodyTapes sources p k r scratch) (SelectedBranchPhases.offset_ge sources p k r) (SelectedBranchPhases.fresh_lt sources p k r scratch) i))=0),
∃ (_words : ∀ ph j,clause.realize.exit (SelectedBranchPhases.body sources p k r scratch
   (CloseoutFinalC10RetainedPhaseFold.tailSlots (SelectedBranchPhases.offset sources p k r)
    (ControllerSelectedContinuation.bodyTapes sources p k r scratch) (SelectedBranchPhases.offset_ge sources p k r) (SelectedBranchPhases.fresh_lt sources p k r scratch)
    (C10TailSlotsUniform.widthSlotT ph j)))=C10BodyWidths.widthWord (width ph) j),
∃ (_blank : ∀ i : Fin 475, (15 ≤ i.val ∧ i.val < 102) ∨ 221 ≤ i.val →
   clause.realize.exit (SelectedBranchPhases.body sources p k r scratch
    (CloseoutFinalC10RetainedPhaseFold.tailSlots (SelectedBranchPhases.offset sources p k r)
     (ControllerSelectedContinuation.bodyTapes sources p k r scratch) (SelectedBranchPhases.offset_ge sources p k r) (SelectedBranchPhases.fresh_lt sources p k r scratch) i))=[]),
SelectedPhaseLayout.branchFuel cost width+2≤remainingFuel

noncomputable def toLoaderSelected (fetchCorrect : IndexFetchProgram.Correct) (semantics : Certificate) (buildSource : SourceBuilder) (sourceProjection : SourceProjection) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (den : Nat) (hden : 0<den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
 (hp : P1Independent.CappedLegalAdmission.passed sources p
  (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
  (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
 (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (remainingFuel : Nat) (width : Phase → Nat) (supplied : (FetchSelected fetchCorrect semantics buildSource sourceProjection) sources p den hden k r scratch n x bits hp site remainingFuel width) : (LoaderRecipes.LoaderSelected semantics buildSource sourceProjection) sources p den hden k r scratch n x bits hp site remainingFuel width := by
 rcases supplied with ⟨cost,penaltySpec,momentSpec,clauseSpec,penalty_kept,moment_kept,threshold,head,words,blank,fits⟩
 let penalty := (fetchBuildPhase fetchCorrect semantics buildSource sourceProjection) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .penalty (SelectedPhaseLayout.S.heads sources p k r scratch) (SelectedPhaseLayout.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) penaltySpec
 let moment := (fetchBuildPhase fetchCorrect semantics buildSource sourceProjection) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .moment penalty.realize.heads penalty.realize.exit (cost .moment) (width .moment) momentSpec
 let clause := (fetchBuildPhase fetchCorrect semantics buildSource sourceProjection) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .clause moment.realize.heads moment.realize.exit (cost .clause) (width .clause) clauseSpec
 exact ⟨cost,(toLoaderPhase fetchCorrect sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .penalty (SelectedPhaseLayout.S.heads sources p k r scratch) (SelectedPhaseLayout.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) penaltySpec),(toLoaderPhase fetchCorrect sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .moment penalty.realize.heads penalty.realize.exit (cost .moment) (width .moment) momentSpec),(toLoaderPhase fetchCorrect sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .clause moment.realize.heads moment.realize.exit (cost .clause) (width .clause) clauseSpec),penalty_kept,moment_kept,threshold,head,words,blank,fits⟩

end FetchRecipes
