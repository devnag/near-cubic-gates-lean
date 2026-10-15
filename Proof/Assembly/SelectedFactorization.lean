import Proof.MachineModel.ControllerSelectedContinuation

/-! Exact factorization of the selected continuation into EntryReady followed by
its original mode switch. The branch definition copies the selected program's
local construction without changing its tape map, phase order, cache or driver. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SelectedEntryFactorization
open NearCubicWires NearCubicWires.P1TopDown
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary RecoveryRootRound
open RepairSource RepairSource.CloseoutFinal RepairSource.VerifierDecoding
open CloseoutRowsOriginalSchedule ControllerSelectedContinuation
noncomputable section

attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size

/-- The actual selected branch, exposing both state count and machine. -/
def branch (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r scratch : Nat)
    (site : Bool → Phase → Σ states, Machine (bodyTapes sources p k r scratch) states) (mode : Bool) :
    Σ states, Machine (WorkspaceSelectedAdmission.originalTapes sources p k+1+1+
      extra sources p k r scratch) states := by
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
  exact ⟨_, branch mode⟩

/-- Equality of the complete dependent program pair, using the explicit branches. -/
theorem program_eq (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r scratch : Nat)
    (site : Bool → Phase → Σ states, Machine (bodyTapes sources p k r scratch) states) :
    ControllerSelectedContinuation.program sources p k r scratch site =
      ⟨_, Composition.machine
        (WorkspaceSelectedEntryReady.program sources p k r (extra sources p k r scratch)
          (by dsimp [extra]; omega)).2
        (CloseoutRowsOriginalSwitch.machine (branch sources p k r scratch site true).2
          (branch sources p k r scratch site false).2
          (WorkspaceSelectedEntryReady.modePort sources p k (extra sources p k r scratch)))⟩ := by
  unfold ControllerSelectedContinuation.program branch
  rfl

/-- The exact frozen diagnostic target, witnessed by the transparent branches. -/
theorem factorization :
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceInterfaces NearCubicWires.P1TopDown in
∀ (sources : EightSources) (gamma : Real) (p : Parameters sources gamma)
  (k r scratch : Nat)
  (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states,
    Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states),
  let extra := ControllerSelectedContinuation.extra sources p k r scratch
  let tapes := WorkspaceSelectedAdmission.originalTapes sources p k+1+1+extra
  ∃ (st sf : Nat) (bt : Machine tapes st) (bf : Machine tapes sf),
    ControllerSelectedContinuation.program sources p k r scratch site =
      ⟨_, Composition.machine (WorkspaceSelectedEntryReady.program sources p k r extra
        (by dsimp [extra,ControllerSelectedContinuation.extra]; omega)).2
        (CloseoutRowsOriginalSwitch.machine bt bf (WorkspaceSelectedEntryReady.modePort sources p k extra))⟩ := by
  intro sources gamma p k r scratch site
  exact ⟨_, _, (branch sources p k r scratch site true).2,
    (branch sources p k r scratch site false).2, program_eq sources p k r scratch site⟩

end
end SelectedEntryFactorization
