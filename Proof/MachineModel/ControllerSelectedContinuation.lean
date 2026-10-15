import Proof.MachineModel.ControllerSelectedLayout
import Proof.MachineModel.TopDownWorkspaceSelectedEntryRuntime
import Proof.CaseAnalysis.FinalFirstPhaseEntry
import Proof.CaseAnalysis.FinalRequestAtCursor
import Proof.CaseAnalysis.RowsGateArityCheck

/-! Recover the complete three-phase continuation syntax at the actual selected
admission layout. This replaces the old state-count-only recipe: both state
count and Machine are exported together. EntryReady supplies the real source
count and the Repeat uses that same driver. Existing retained folds and tail
are reused. The site callback and length-only remaining fuel are explicit
construction inputs, not claimed closed by assembling the syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.ControllerSelectedContinuation
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary RecoveryRootRound
open RepairSource RepairSource.CloseoutFinal RepairSource.VerifierDecoding
open CloseoutRowsOriginalSchedule
noncomputable section

def extra (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r scratch : Nat) := WorkspaceSelectedEntry.size sources k r p.clauseDegree+1155+scratch

def bodyTapes (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r scratch : Nat) := WorkspaceSelectedAdmission.originalTapes sources p k+2+extra sources p k r scratch-4

attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size

@[irreducible] def program (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r scratch : Nat)
    (site : Bool → Phase → Σ states, Machine (bodyTapes sources p k r scratch) states) :
    Σ states, Machine (WorkspaceSelectedAdmission.originalTapes sources p k+1+1+extra sources p k r scratch) states := by
  let t := WorkspaceSelectedAdmission.originalTapes sources p k
  let P := WorkspaceSelectedEntry.size sources k r p.clauseDegree
  let X := extra sources p k r scratch
  let B := bodyTapes sources p k r scratch
  let L := P+t-2
  have ht : 2 ≤ t := WorkspaceSelectedEntryReady.old_size sources p k
  have hP : 302 ≤ P := by dsimp only [P]; unfold WorkspaceSelectedEntry.size; omega
  have hspace : P+1155 ≤ X := by dsimp [X, extra, P]; omega
  have hL : 301 ≤ L := by dsimp [L]; omega
  have hFresh : L+1154 < B := by dsimp [L, B, bodyTapes]; change P+t-2+1154 < t+2+X-4; omega
  let body := ControllerSelectedLayout.selectedBody sources p k r X hspace
  let loops := WorkspaceSelectedEntryRepeat.slots body
    (WorkspaceSelectedEntryReady.driver sources p k r X (by omega))
  let cache : Bool → Fin 19 → Fin B := fun mode j =>
    let c := WorkspaceSelectedEntryReady.cache sources p k mode j
    ⟨if c.val<2 then c.val else P+c.val-2, by
      have hc := c.isLt
      change c.val<t at hc
      dsimp [B, bodyTapes]
      change (if c.val<2 then c.val else P+c.val-2)<t+2+X-4
      split_ifs <;> omega⟩
  let tail := RecoveryFocus.machine body
    (RecoveryFocus.machine (CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh)
      (C10TailComposeUniform.tailMachine sources))
  let branch := fun mode : Bool =>
    let slots := cache mode
    let right := DecompositionCountPosition.move (fun i : Fin B =>
      if i=slots 13 ∨ i=slots 14 then .right else .stay)
    let left := DecompositionCountPosition.move (fun i : Fin B =>
      if i=slots 13 ∨ i=slots 14 then .left else .stay)
    let query := RecoveryFocus.machine slots PCPPQueryClauseReuse.machine
    let advance := RecoveryFocus.machine slots CloseoutFinalC10RequestAtCursor.advance
    let terminalSlots : Fin 4 → Fin B := ![slots 14,⟨L+53,by omega⟩,slots 1,slots 2]
    let test := RecoveryFocus.machine terminalSlots CloseoutRowsGateArityCheck.machine
    let clear := C10LengthGate.branch (slots 2) (slots 1) (CloseoutRowsOriginalSwitch.stop B)
    let phaseEntry : Phase → Σ states, Machine B states := fun ph => match ph with
      | .penalty => ⟨_,CloseoutFinalC10FirstPhaseEntry.machine L B hL (by omega)⟩
      | .moment | .clause => ⟨_,RecoveryFocus.machine slots
          (RecoveryFocus.machine (![14,17,18] : Fin 3 → Fin 19) (RecoveryScratchErase.resetMachine 1))⟩
    let phase := fun ph : Phase =>
      let live := Composition.machine right
        (Composition.machine query (Composition.machine left
          (Composition.machine (site mode ph).2
            (Composition.machine right (Composition.machine advance left)))))
      let clause := Composition.machine test (CloseoutRowsOriginalSwitch.machine clear live (slots 1))
      let loop := RecoveryFocus.machine loops (RepeatMachine.machine clause (fun _ _=>true))
      Composition.machine (RecoveryFocus.machine body (phaseEntry ph).2)
        (Composition.machine loop
          (RecoveryFocus.machine body (CloseoutFinalC10RetainedPhaseFold.machine L B hL hFresh ph)))
    Composition.machine (phase .penalty)
      (Composition.machine (phase .moment) (Composition.machine (phase .clause) tail))
  exact ⟨_,Composition.machine (WorkspaceSelectedEntryReady.program sources p k r X (by omega)).2
    (CloseoutRowsOriginalSwitch.machine (branch true) (branch false)
      (WorkspaceSelectedEntryReady.modePort sources p k X))⟩

/-- The hierarchy index follows the previously chosen polynomial-N degrees.
The code depends on fixed source parameters and the fixed site, never on live
length, input word, or guessed description. Whole admitted correctness and
the bound on `remainingFuel` must still be supplied at this very machine. -/
def continuation (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (remainingDegree r base scratch : Nat)
    (site : Bool → Phase → Σ states, Machine (bodyTapes sources p
      (SelectedRuntime.hierarchyIndex sources p (WorkspaceSelectedEntryRuntime.degree sources p remainingDegree))
      r scratch) states)
    (remainingFuel : Nat → Nat) : SelectedAssembly.ContinuationData sources p := by
  let degree := WorkspaceSelectedEntryRuntime.degree sources p remainingDegree
  let k := SelectedRuntime.hierarchyIndex sources p degree
  let X := extra sources p k r scratch
  let built := program sources p k r scratch site
  let result : Fin (WorkspaceSelectedAdmission.originalTapes sources p k+1+1+X) :=
    ⟨WorkspaceSelectedAdmission.originalTapes sources p k+2+217,by
      have hP : 302 ≤ WorkspaceSelectedEntry.size sources k r p.clauseDegree := by
        unfold WorkspaceSelectedEntry.size; omega
      dsimp [X, extra]; omega⟩
  exact SelectedRuntime.continuation sources p degree base X built.2 result
    (WorkspaceSelectedEntryRuntime.fuel sources p k r remainingFuel)

end
end NearCubicWires.P1TopDown.ControllerSelectedContinuation
