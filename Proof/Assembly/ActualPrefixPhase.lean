import Proof.CaseAnalysis.FinalPartsSchedule
import Proof.CaseAnalysis.FinalStageFields
import Proof.Assembly.ActualPrefixSource
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

namespace ActualPrefixRecipes
open NativeFamilyGenerator

noncomputable abbrev GeneratedPhase (g : Data) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k den r scratch : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (n : Nat) (x : BitInput n)
 (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
 (bits : List Bool)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states,
   Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
 (hin : Fin (SelectedBranchPhases.tapes sources p k r scratch) → Nat)
 (tin : Fin (SelectedBranchPhases.tapes sources p k r scratch) → List Bool)
 (fuel width : Nat) : Prop :=
let pcpp := pcppAt sources k clock x oracle
 let Atom := C10TotalDecode.Atom pcpp
 let constants := NearCubicWires.RepairSource.CloseoutFinal.constantsOf sources
 let coordinate := CappedCoordinates.coordinate sources k clock p den x oracle bits
 let systematicAtom := C10TotalDecode.Atom.systematic (pcpp := pcpp)
 let evaluate := C10TotalDecode.evaluate (pcpp := pcpp)
 let mass : Real := ((CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom).coefficientMass : Rat)
 let L := SelectedBranchPhases.offset sources p k r
 let B := ControllerSelectedContinuation.bodyTapes sources p k r scratch
 let hL := SelectedBranchPhases.offset_ge sources p k r
 let hFresh := SelectedBranchPhases.fresh_lt sources p k r scratch
 let t := SelectedBranchPhases.tapes sources p k r scratch
 let body := SelectedBranchPhases.body sources p k r scratch
 let driver := SelectedBranchPhases.driver sources p k r scratch
 let target := NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields.stageTarget sources p 0
 let b := C10PartsSchedule.entryWidthSchedule sources k r n
 ∃ (liveScale : Nat)
   (limits : CanonicalWitnessCodec.LegalSumLimits) (denBits : Nat)
   (order : List (CircuitMonomial Atom 4)),
 let supplier := supplier sources liveScale target mode (pcpp := pcpp)
 let failure := failure target
 ∃ (entries : List NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream.Entry)
    (H : Nat → Fin B → Nat)
    (A : Nat → Fin B → List Bool)
    (entryFuel : Nat)
    (N : Nat)
    (cost : Nat)
    (middleH : Fin t → Nat)
    (middle : Fin t → List Bool)
    (_horder : (CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom).monomials.Perm order)
    (_hrecords : List.Forall₂ (fun m e =>
      e.coefficient = CloseoutFinalC10SupplierCalls.coefficientEstimate m.coefficient ∧
      e.count = (CloseoutFinalC10ModeNativeStageFields.modeEstimate sources liveScale target mode m.factors).num ∧
      e.denominator = (CloseoutFinalC10ModeNativeStageFields.modeEstimate sources liveScale target mode m.factors).den)
      order entries)
    (_hmass : (CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom).coefficientMass ≤
      C10FamilyMass.siteMassBound limits.coefficientMassCap ph)
    (_hcoeff : CloseoutFinalC10SupplierCalls.CoefficientsFit b
      (CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom))
    (_htarget : C10SupplierAccuracyChain.accuracyTarget constants limits ph ≤ target)
    (_htargetpos : 0 < target)
    (_hden : ∀ m ∈ order,
      (CloseoutFinalC10ModeNativeStageFields.modeEstimate sources liveScale target mode m.factors).den ≤ 2^denBits)
    (_hdenwidth : denBits+1 ≤ b)
    (_hHw : ∀ i, H N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph i) = 0)
    (_hHf : ∀ i, H N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph i) = 0)
    (_hwidthDriver : A N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph 218) = List.replicate b true)
    (_hcount : A N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph 90) = NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word entries.length)
    (_hstream : A N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph 81) = NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream.words b entries)
    (_hblank : ∀ i : Fin 278, 2 ≤ i.val → i.val < 215 → i.val ≠ 81 → i.val ≠ 90 → A N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph i)=[])
    (_hfresh : ∀ i : Fin 278, 219 ≤ i.val → A N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph i)=[])
    (_hrecord : A N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph 215)=[])
    (_hlog : A N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph 218)=[])
    (_hentry : Step (RecoveryFocus.machine body (SelectedBranchPhases.phaseEntry sources p k r scratch mode ph).2)
      entryFuel hin tin middleH middle)
    (_hhead : ∀ i, middleH (body i)=H 0 i)
    (_htape : ∀ i, middle (body i)=A 0 i)
    (_hdriver : middleH driver=1)
    (_hword : middle driver=UnaryTemplate.tape N)
    (_hN : N=2^pcpp.clauseBits)
    (siteFuel : Nat)
    (_hcost : 4*N+PCPPQueryCachedBounds.callBudget (CloseoutLanguage.selectedPCPP sources)
       ((req sources k clock x oracle).circuit.size+(req sources k clock x oracle).arity)+siteFuel+21≤cost)
    (s_after : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool)
    (_s_head : ∀ (j : Nat), j≤2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits → ∀ (i : Fin 19),H j (SelectedBranchPhases.cache sources p k r scratch mode i)=0)
    (_s_terminal_head : ∀ (j : Nat),j<2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits → H j (LiveClauseSites.Selected.terminal sources p k r scratch)=0)
    (_s_count : ∀ (j : Nat),j<2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits → A j (LiveClauseSites.Selected.terminal sources p k r scratch)=
   List.replicate (2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits) true)
    (_s_cached : ∀ (j : Nat),j<2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits → ∀ (i : Fin 19),A j (SelectedBranchPhases.cache sources p k r scratch mode i)=
   PCPPQueryIndexPadding.clauseData (pcppOutput (req sources k clock x oracle) ((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle))) (req sources k clock x oracle).arity j
   (PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP sources) ((req sources k clock x oracle).circuit.size+(req sources k clock x oracle).arity)) [] i)
    (_s_source : ∀ ci : Fin (2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits),
      GeneratedSourceSpec g sources p k den r scratch clock n x oracle bits site mode ph ci
       (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) liveScale target b siteFuel)
    (_s_restored : ∀ (j : Nat),j<2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits → ∀ (i : Fin 19),s_after j (SelectedBranchPhases.cache sources p k r scratch mode i)=
   PCPPQueryIndexPadding.clauseData (pcppOutput (req sources k clock x oracle) ((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle))) (req sources k clock x oracle).arity j
   (PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP sources) ((req sources k clock x oracle).circuit.size+(req sources k clock x oracle).arity)) [] i)
    (_s_next : ∀ (j : Nat),j<2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits → A (j+1)=
   install (SelectedBranchPhases.cache sources p k r scratch mode) (s_after j)
    (PCPPQueryIndexPadding.clauseData (pcppOutput (req sources k clock x oracle) ((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle))) (req sources k clock x oracle).arity (j+1)
     (PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP sources) ((req sources k clock x oracle).circuit.size+(req sources k clock x oracle).arity)) [])),
 fuel=entryFuel+1+(N*(cost+3)+3+1+CloseoutFinalC10RetainedPhaseFold.fuel b entries.length) ∧
 width=CloseoutFinalC10WorkerFold.foldWidth (CompetitorRationalDecision.width b) entries

noncomputable def toFetchPhase (g : Data) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k den r scratch : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (n : Nat) (x : BitInput n)
 (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
 (bits : List Bool)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states,
   Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
 (hin : Fin (SelectedBranchPhases.tapes sources p k r scratch) → Nat)
 (tin : Fin (SelectedBranchPhases.tapes sources p k r scratch) → List Bool)
 (fuel width : Nat) (supplied : GeneratedPhase g sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width) : FetchRecipes.FetchPhase sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width := by
 let target := NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields.stageTarget sources p 0
 let b := C10PartsSchedule.entryWidthSchedule sources k r n
 rcases supplied with ⟨liveScale,limits,denBits,order,entries,H,A,entryFuel,N,cost,middleH,middle,horder,hrecords,hmass,hcoeff,htarget,htargetpos,hden,hdenwidth,_hHw,_hHf,_hwidthDriver,_hcount,_hstream,_hblank,_hfresh,_hrecord,_hlog,_hentry,_hhead,_htape,_hdriver,_hword,_hN,siteFuel,_hcost,s_after,s_head,s_terminal_head,s_count,s_cached,s_source,s_restored,s_next,hfuel,hwidth⟩
 exact ⟨liveScale,target,limits,denBits,order,b,entries,H,A,entryFuel,N,cost,middleH,middle,horder,hrecords,hmass,hcoeff,htarget,htargetpos,hden,hdenwidth,_hHw,_hHf,_hwidthDriver,_hcount,_hstream,_hblank,_hfresh,_hrecord,_hlog,_hentry,_hhead,_htape,_hdriver,_hword,_hN,siteFuel,_hcost,s_after,s_head,s_terminal_head,s_count,s_cached,(fun ci => toFetchSource g sources p k den r scratch clock n x oracle bits site mode ph ci (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) liveScale target b siteFuel (s_source ci)),s_restored,s_next,hfuel,hwidth⟩

noncomputable def generatedBuildPhase (g : Data) (fetchCorrect : IndexFetchProgram.Correct) (semantics : Certificate) (buildSource : SourceBuilder) (sourceProjection : SourceProjection) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k den r scratch : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (n : Nat) (x : BitInput n)
 (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
 (bits : List Bool)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states,
   Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
 (hin : Fin (SelectedBranchPhases.tapes sources p k r scratch) → Nat)
 (tin : Fin (SelectedBranchPhases.tapes sources p k r scratch) → List Bool)
 (fuel width : Nat) (supplied : GeneratedPhase g sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width) :
 OrderedCallPhases.PhaseConstruction.Input sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width := FetchRecipes.fetchBuildPhase fetchCorrect semantics buildSource sourceProjection sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width
  (toFetchPhase g sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width supplied)

end ActualPrefixRecipes
