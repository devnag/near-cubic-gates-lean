import Proof.Assembly.SelectedFactorization
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SelectedEntryExecution
open NearCubicWires NearCubicWires.P1TopDown
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource RepairSource.CloseoutFinal RepairSource.VerifierDecoding
open CloseoutRowsOriginalSchedule ControllerSelectedContinuation
open SelectedEntryFactorization
noncomputable section
attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size branch

theorem selected_program_run (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r scratch : Nat)
    (site : Bool → Phase → Σ states, Machine (bodyTapes sources p k r scratch) states)
    (entryCost branchCost : Nat)
    (H0 HM HF : Fin (WorkspaceSelectedAdmission.originalTapes sources p k+1+1+extra sources p k r scratch) → Nat)
    (A0 AM AF : Fin (WorkspaceSelectedAdmission.originalTapes sources p k+1+1+extra sources p k r scratch) → List Bool)
    (hentry : Step (WorkspaceSelectedEntryReady.program sources p k r (extra sources p k r scratch)
      (by dsimp [extra]; omega)).2 entryCost H0 A0 HM AM)
    (hbranch : Step (branch sources p k r scratch site
      (readTapeBit (AM (WorkspaceSelectedEntryReady.modePort sources p k (extra sources p k r scratch)))
        (HM (WorkspaceSelectedEntryReady.modePort sources p k (extra sources p k r scratch))))).2
      branchCost HM AM HF AF) :
    Step (ControllerSelectedContinuation.program sources p k r scratch site).2
      (entryCost+1+(branchCost+2)) H0 A0 HF AF := by
  have switched : Step (CloseoutRowsOriginalSwitch.machine (branch sources p k r scratch site true).2
      (branch sources p k r scratch site false).2
      (WorkspaceSelectedEntryReady.modePort sources p k (extra sources p k r scratch)))
      (branchCost+2) HM AM HF AF := by
    cases hb : readTapeBit (AM (WorkspaceSelectedEntryReady.modePort sources p k (extra sources p k r scratch)))
      (HM (WorkspaceSelectedEntryReady.modePort sources p k (extra sources p k r scratch))) with
    | false => rw [hb] at hbranch; exact CloseoutRowsOriginalSwitch.false_run _ _ _ hbranch hb
    | true => rw [hb] at hbranch; exact CloseoutRowsOriginalSwitch.true_run _ _ _ hbranch hb
  have assembled := hentry.seq switched
  unfold ControllerSelectedContinuation.program branch at *
  exact assembled

/-- The exact backward boundary after the selected entry: actual intermediate
heads/tapes, entry receipt, complete chosen branch realization, and full cost. -/
structure PhaseInput (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r scratch : Nat)
    (site : Bool → Phase → Σ states, Machine (bodyTapes sources p k r scratch) states)
    {Atom : Type} {n : Nat} {circuit : BooleanCircuit n}
    {source : RepairRepresentation.PointwisePCPPAlgorithm}
    (ph : Phase) (constants : CompetitorRationalGap.Constants source)
    (pcpp : SourceInterfaces.PointwisePCPP circuit)
    (proofValue : BitInput n → Fin (pcpp.systematicBits+pcpp.auxiliaryBits) → Real)
    (evaluate : Atom → BitInput n → Bool) (budget : Nat)
    (hin : Fin (WorkspaceSelectedAdmission.originalTapes sources p k+1+1+extra sources p k r scratch) → Nat)
    (tin : Fin (WorkspaceSelectedAdmission.originalTapes sources p k+1+1+extra sources p k r scratch) → List Bool)
    (port : Fin (WorkspaceSelectedAdmission.originalTapes sources p k+1+1+extra sources p k r scratch))
    (width : Nat) : Type 1 where
  entryCost : Nat
  branchCost : Nat
  heads : Fin (WorkspaceSelectedAdmission.originalTapes sources p k+1+1+extra sources p k r scratch) → Nat
  tapes : Fin (WorkspaceSelectedAdmission.originalTapes sources p k+1+1+extra sources p k r scratch) → List Bool
  entry : Step (WorkspaceSelectedEntryReady.program sources p k r (extra sources p k r scratch)
    (by dsimp [extra]; omega)).2 entryCost hin tin heads tapes
  branchResult : CloseoutFinalC10Realizes.Realizes ph constants pcpp proofValue evaluate
    (branch sources p k r scratch site
      (readTapeBit (tapes (WorkspaceSelectedEntryReady.modePort sources p k (extra sources p k r scratch)))
        (heads (WorkspaceSelectedEntryReady.modePort sources p k (extra sources p k r scratch))))).2
    branchCost heads tapes port width
  fits : entryCost+1+(branchCost+2)≤budget

def PhaseInput.realizes {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {k r scratch : Nat}
    {site : Bool → Phase → Σ states, Machine (bodyTapes sources p k r scratch) states}
    {Atom : Type} {n : Nat} {circuit : BooleanCircuit n}
    {source : RepairRepresentation.PointwisePCPPAlgorithm}
    {ph : Phase} {constants : CompetitorRationalGap.Constants source}
    {pcpp : SourceInterfaces.PointwisePCPP circuit}
    {proofValue : BitInput n → Fin (pcpp.systematicBits+pcpp.auxiliaryBits) → Real}
    {evaluate : Atom → BitInput n → Bool} {budget : Nat}
    {hin : Fin (WorkspaceSelectedAdmission.originalTapes sources p k+1+1+extra sources p k r scratch) → Nat}
    {tin : Fin (WorkspaceSelectedAdmission.originalTapes sources p k+1+1+extra sources p k r scratch) → List Bool}
    {port : Fin (WorkspaceSelectedAdmission.originalTapes sources p k+1+1+extra sources p k r scratch)}
    {width : Nat}
    (I : PhaseInput sources p k r scratch site ph constants pcpp proofValue evaluate budget hin tin port width) :
    CloseoutFinalC10Realizes.Realizes ph constants pcpp proofValue evaluate
      (ControllerSelectedContinuation.program sources p k r scratch site).2 budget hin tin port width :=
  C10TailComposeVerdict.transport I.branchResult I.branchResult.heads I.branchResult.exit
    ((selected_program_run sources p k r scratch site I.entryCost I.branchCost
      hin I.heads I.branchResult.heads tin I.tapes I.branchResult.exit I.entry I.branchResult.run).enlarge I.fits)
    I.branchResult.hencoded

end
end SelectedEntryExecution
