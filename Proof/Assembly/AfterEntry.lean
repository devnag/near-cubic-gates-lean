import Proof.Assembly.CappedReady

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace CappedEntryRun
open NearCubicWires NearCubicWires.P1TopDown
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource SourceInterfaces RepairSource.CloseoutFinal
open ControllerSelectedContinuation
open SelectedEntryFactorization (branch)
noncomputable section
attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size branch

theorem space (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r scratch : Nat) :
    WorkspaceSelectedEntry.size sources k r p.clauseDegree+96 ≤ extra sources p k r scratch := by
  dsimp [extra]; omega

/-- Only the complete selected branch remains: the entry state and its physical
execution are constructed from the actual capped admission in CappedReady. -/
structure AfterEntry (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states,
      Machine (bodyTapes sources p k r scratch) states)
    {Atom : Type} {arity : Nat} {circuit : BooleanCircuit arity}
    {source : RepairRepresentation.PointwisePCPPAlgorithm}
    (ph : CloseoutRowsOriginalSchedule.Phase) (constants : CompetitorRationalGap.Constants source)
    (pcpp : PointwisePCPP circuit)
    (proofValue : BitInput arity → Fin (pcpp.systematicBits+pcpp.auxiliaryBits) → Real)
    (evaluate : Atom → BitInput arity → Bool) (remainingFuel : Nat)
    (port : Fin (WorkspaceSelectedAdmission.originalTapes sources p k+1+1+extra sources p k r scratch))
    (width : Nat) : Type 1 where
  cost : Nat
  result :
    let X := extra sources p k r scratch
    let hs := space sources p k r scratch
    let H := WorkspaceSelectedEntryReady.finalHeads sources p k r X hs
    let A := readyBank sources p den hden k r X hs n x bits hp
    CloseoutFinalC10Realizes.Realizes ph constants pcpp proofValue evaluate
      (branch sources p k r scratch site
        (readTapeBit (A (WorkspaceSelectedEntryReady.modePort sources p k X))
          (H (WorkspaceSelectedEntryReady.modePort sources p k X)))).2
      cost H A port width
  fits : cost+2 ≤ remainingFuel

def AfterEntry.phaseInput {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool}
    {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true}
    {site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states,
      Machine (bodyTapes sources p k r scratch) states}
    {Atom : Type} {arity : Nat} {circuit : BooleanCircuit arity}
    {source : RepairRepresentation.PointwisePCPPAlgorithm}
    {ph : CloseoutRowsOriginalSchedule.Phase} {constants : CompetitorRationalGap.Constants source}
    {pcpp : PointwisePCPP circuit}
    {proofValue : BitInput arity → Fin (pcpp.systematicBits+pcpp.auxiliaryBits) → Real}
    {evaluate : Atom → BitInput arity → Bool} {remainingFuel : Nat}
    {port : Fin (WorkspaceSelectedAdmission.originalTapes sources p k+1+1+extra sources p k r scratch)}
    {width : Nat}
    (R : AfterEntry sources p den hden k r scratch n x bits hp site ph constants pcpp proofValue evaluate
      remainingFuel port width) :
    SelectedEntryExecution.PhaseInput sources p k r scratch site ph constants pcpp proofValue evaluate
      (WorkspaceSelectedEntryBudget.envelope sources p k r n+1+remainingFuel) (fun _ => 0)
      (initialBank sources p den hden k (extra sources p k r scratch) n x bits) port width where
  entryCost := WorkspaceSelectedEntryBudget.envelope sources p k r n
  branchCost := R.cost
  heads := WorkspaceSelectedEntryReady.finalHeads sources p k r (extra sources p k r scratch)
    (space sources p k r scratch)
  tapes := readyBank sources p den hden k r (extra sources p k r scratch)
    (space sources p k r scratch) n x bits hp
  entry := ready_step sources p den hden k r (extra sources p k r scratch)
    (space sources p k r scratch) n x bits hp
  branchResult := R.result
  fits := by have h := R.fits; omega

end
end CappedEntryRun
