import Proof.Assembly.NativeSelected
import Proof.Assembly.NativeNativePhase

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

namespace NativeRecipes

noncomputable abbrev NativeSelected (buildSource : SourceBuilder) (sourceProjection : SourceProjection) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (den : Nat) (hden : 0<den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
 (hp : P1Independent.CappedLegalAdmission.passed sources p
  (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
  (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
 (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (remainingFuel : Nat) (width : Phase → Nat) : Prop :=
∃ (cost : Phase → Nat),
∃ (penaltySpec : NativePhase sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .penalty (SelectedPhaseLayout.S.heads sources p k r scratch) (SelectedPhaseLayout.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty)),
let penalty := (nativeBuildPhase buildSource sourceProjection) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .penalty (SelectedPhaseLayout.S.heads sources p k r scratch) (SelectedPhaseLayout.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) penaltySpec
∃ (momentSpec : NativePhase sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .moment penalty.realize.heads penalty.realize.exit (cost .moment) (width .moment)),
let moment := (nativeBuildPhase buildSource sourceProjection) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .moment penalty.realize.heads penalty.realize.exit (cost .moment) (width .moment) momentSpec
∃ (clauseSpec : NativePhase sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .clause moment.realize.heads moment.realize.exit (cost .clause) (width .clause)),
let clause := (nativeBuildPhase buildSource sourceProjection) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .clause moment.realize.heads moment.realize.exit (cost .clause) (width .clause) clauseSpec
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

noncomputable def selectedProjection (buildSource : SourceBuilder) (sourceProjection : SourceProjection) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (den : Nat) (hden : 0<den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
 (hp : P1Independent.CappedLegalAdmission.passed sources p
  (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
  (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
 (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (remainingFuel : Nat) (width : Phase → Nat) (supplied : (NativeSelected buildSource sourceProjection) sources p den hden k r scratch n x bits hp site remainingFuel width) : (ExpandedSelected buildSource) sources p den hden k r scratch n x bits hp site remainingFuel width := by
 rcases supplied with ⟨cost,penaltySpec,momentSpec,clauseSpec,penalty_kept,moment_kept,threshold,head,words,blank,fits⟩
 let penalty := (nativeBuildPhase buildSource sourceProjection) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .penalty (SelectedPhaseLayout.S.heads sources p k r scratch) (SelectedPhaseLayout.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) penaltySpec
 let moment := (nativeBuildPhase buildSource sourceProjection) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .moment penalty.realize.heads penalty.realize.exit (cost .moment) (width .moment) momentSpec
 let clause := (nativeBuildPhase buildSource sourceProjection) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .clause moment.realize.heads moment.realize.exit (cost .clause) (width .clause) clauseSpec
 exact ⟨cost,((toPhase sourceProjection) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .penalty (SelectedPhaseLayout.S.heads sources p k r scratch) (SelectedPhaseLayout.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) penaltySpec),((toPhase sourceProjection) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .moment penalty.realize.heads penalty.realize.exit (cost .moment) (width .moment) momentSpec),((toPhase sourceProjection) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .clause moment.realize.heads moment.realize.exit (cost .clause) (width .clause) clauseSpec),penalty_kept,moment_kept,threshold,head,words,blank,fits⟩

noncomputable abbrev NativeRecipe : Prop :=
∀ (buildSource : SourceBuilder)
 (sourceProjection : SourceProjection),
∃ (capIndex : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat)),
∃ (remainingDegree : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat)),
∃ (r : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat)),
∃ (base : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat)),
∃ (scratch : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat)),
∃ (site : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Bool → NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule.Phase → Σ states,
 NearCubicWires.LocalBitMultitape.Machine
 (NearCubicWires.P1TopDown.ControllerSelectedContinuation.bodyTapes sources p
  (NearCubicWires.P1TopDown.ControllerCappedRuntime.hierarchyIndex sources p
   (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p))
  (r sources gamma hg hh p) (scratch sources gamma hg hh p)) states)),
∃ (remainingFuel : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat → Nat)),
∃ (widths : (open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule NearCubicWires.RepairSource.CloseoutFinal.C10GuardedMachineConsumer NearCubicWires.RepairSource.CloseoutFinal.C10GuardedStageConsumer NearCubicWires.RepairSource.CloseoutFinal.C10Fusion NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode NearCubicWires.P1TopDown in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → (n : Nat) → (x : BitInput n) → (bits : List Bool) → Phase → Nat)),
∃ (phaseConstruction : (open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule NearCubicWires.RepairSource.CloseoutFinal.C10GuardedMachineConsumer NearCubicWires.RepairSource.CloseoutFinal.C10GuardedStageConsumer NearCubicWires.RepairSource.CloseoutFinal.C10Fusion NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode NearCubicWires.P1TopDown in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → (n : Nat) → (x : BitInput n) → (bits : List Bool) → let C := NearCubicWires.P1TopDown.ControllerCappedRuntime.continuation sources p (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p) (r sources gamma hg hh p) (base sources gamma hg hh p) (scratch sources gamma hg hh p) (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p); (hn : (ControllerCappedSelected.workerData sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData (capIndex sources gamma hg hh p+1) C)).onset ≤ n) → (hp : (ControllerCappedSelected.workerData sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData (capIndex sources gamma hg hh p+1) C)).passed n x bits = true) → (NativeSelected buildSource sourceProjection) sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) C.k (r sources gamma hg hh p) (scratch sources gamma hg hh p) n x bits hp (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p n) (widths sources gamma hg hh p n x bits))),
∃ (remainingCoefficient : ((sources : NearCubicWires.RepairSource.EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : NearCubicWires.RepairSource.CloseoutFinal.Parameters sources gamma) → Nat)),
∃ (remainingOnset : ((sources : NearCubicWires.RepairSource.EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : NearCubicWires.RepairSource.CloseoutFinal.Parameters sources gamma) → Nat)),
∃ (tableCoefficient : ((sources : NearCubicWires.RepairSource.EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : NearCubicWires.RepairSource.CloseoutFinal.Parameters sources gamma) → Nat)),
∃ (tableDegree : ((sources : NearCubicWires.RepairSource.EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : NearCubicWires.RepairSource.CloseoutFinal.Parameters sources gamma) → Nat)),
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.P1TopDown in
∀ (sources : EightSources) (gamma : Real) (hg : 0<gamma) (hh : gamma<1/2) (p : Parameters sources gamma),
 let C := ControllerCappedRuntime.continuation sources p (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p) (r sources gamma hg hh p) (base sources gamma hg hh p) (scratch sources gamma hg hh p) (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p);
 ∀ n, remainingOnset sources gamma hg hh p≤n → remainingFuel sources gamma hg hh p n+3≤
 remainingCoefficient sources gamma hg hh p*(n+1)^(remainingDegree sources gamma hg hh p)+
 tableCoefficient sources gamma hg hh p*(2^(SelectedRuntime.width C n-(SelectedRuntime.sigma sources+tableDegree sources gamma hg hh p+2)*
 SelectedRuntime.logarithm C n)*(SelectedRuntime.width C n+1)^(tableDegree sources gamma hg hh p))

end NativeRecipes
