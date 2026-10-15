import Proof.Assembly.NativePhase
import Proof.Assembly.NativeNativeSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

namespace NativeRecipes

noncomputable abbrev NativePhase (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
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
 ∃ (supplier : List Atom → Rat)
    (failure : Real)
    (b : Nat)
    (entries : List NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream.Entry)
    (H : Nat → Fin B → Nat)
    (A : Nat → Fin B → List Bool)
    (entryFuel : Nat)
    (N : Nat)
    (cost : Nat)
    (middleH : Fin t → Nat)
    (middle : Fin t → List Bool)
    (_hfailure : 0 ≤ failure)
    (_hpoint : ∀ monomial ∈ (NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom).monomials, |((supplier monomial.factors : Rat) : Real) - NearCubicWires.SupplierPipeline.conjunctionProbability evaluate monomial.factors| ≤ failure)
    (_hbudget : failure * mass ≤ ((NearCubicWires.RepairSource.CompetitorRationalGap.estimationTolerance constants (NearCubicWires.RepairSource.CompetitorRationalGap.zeta constants) : Rat) : Real))
    (_hcalls : OrderedCallPhases.OrderedCalls supplier (NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom).monomials entries)
    (_hvalid : ∀ entry ∈ entries, NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream.Entry.Valid b entry)
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
      NativeSourceSpec sources p k den r scratch clock n x oracle bits site mode ph ci
       (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) b siteFuel)
    (_s_restored : ∀ (j : Nat),j<2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits → ∀ (i : Fin 19),s_after j (SelectedBranchPhases.cache sources p k r scratch mode i)=
   PCPPQueryIndexPadding.clauseData (pcppOutput (req sources k clock x oracle) ((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle))) (req sources k clock x oracle).arity j
   (PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP sources) ((req sources k clock x oracle).circuit.size+(req sources k clock x oracle).arity)) [] i)
    (_s_next : ∀ (j : Nat),j<2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits → A (j+1)=
   install (SelectedBranchPhases.cache sources p k r scratch mode) (s_after j)
    (PCPPQueryIndexPadding.clauseData (pcppOutput (req sources k clock x oracle) ((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle))) (req sources k clock x oracle).arity (j+1)
     (PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP sources) ((req sources k clock x oracle).circuit.size+(req sources k clock x oracle).arity)) [])),
 fuel=entryFuel+1+(N*(cost+3)+3+1+CloseoutFinalC10RetainedPhaseFold.fuel b entries.length) ∧
 width=CloseoutFinalC10WorkerFold.foldWidth (CompetitorRationalDecision.width b) entries

noncomputable def toPhase (sourceProjection : SourceProjection) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k den r scratch : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (n : Nat) (x : BitInput n)
 (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
 (bits : List Bool)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states,
   Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
 (hin : Fin (SelectedBranchPhases.tapes sources p k r scratch) → Nat)
 (tin : Fin (SelectedBranchPhases.tapes sources p k r scratch) → List Bool)
 (fuel width : Nat) (supplied : NativePhase sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width) : ExpandedPhase sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width := by
 rcases supplied with ⟨supplier,failure,b,entries,H,A,entryFuel,N,cost,middleH,middle,_hfailure,_hpoint,_hbudget,_hcalls,_hvalid,_hHw,_hHf,_hwidthDriver,_hcount,_hstream,_hblank,_hfresh,_hrecord,_hlog,_hentry,_hhead,_htape,_hdriver,_hword,_hN,siteFuel,_hcost,s_after,s_head,s_terminal_head,s_count,s_cached,s_source,s_restored,s_next,hfuel,hwidth⟩
 refine ⟨supplier,failure,b,entries,H,A,entryFuel,N,cost,middleH,middle,_hfailure,_hpoint,_hbudget,_hcalls,_hvalid,_hHw,_hHf,_hwidthDriver,_hcount,_hstream,_hblank,_hfresh,_hrecord,_hlog,_hentry,_hhead,_htape,_hdriver,_hword,_hN,siteFuel,_hcost,s_after,s_head,s_terminal_head,s_count,s_cached,?_,s_restored,s_next,hfuel,hwidth⟩
 intro ci
 exact sourceProjection sources p k den r scratch clock n x oracle bits site mode ph ci (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) b siteFuel (s_source ci)

noncomputable def nativeBuildPhase (buildSource : SourceBuilder) (sourceProjection : SourceProjection) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k den r scratch : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (n : Nat) (x : BitInput n)
 (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
 (bits : List Bool)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states,
   Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
 (hin : Fin (SelectedBranchPhases.tapes sources p k r scratch) → Nat)
 (tin : Fin (SelectedBranchPhases.tapes sources p k r scratch) → List Bool)
 (fuel width : Nat) (supplied : NativePhase sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width) :
 OrderedCallPhases.PhaseConstruction.Input sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width := (buildPhase buildSource) sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width ((toPhase sourceProjection) sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width supplied)

end NativeRecipes
