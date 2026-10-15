import Proof.Assembly.CappedEntryFuel
import Proof.Assembly.CappedOriginals
import Proof.Assembly.EntryRunFromFacts
import Proof.Assembly.SelectedExecution

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace CappedEntryRun
open NearCubicWires NearCubicWires.P1TopDown
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary RecoveryRootRound
open RepairSource SourceInterfaces RepairSource.CloseoutFinal
open WorkspaceSelectedAdmission (originalTapes)
open WorkspaceSelectedProgram (finalBank)
noncomputable section
attribute [local irreducible] originalTapes WorkspaceSelectedEntry.size

variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
  (den : Nat) (hden : 0 < den) (k r extra : Nat)
  (hspace : WorkspaceSelectedEntry.size sources k r p.clauseDegree+96 ≤ extra)
  (n : Nat) (x : BitInput n) (bits : List Bool)

def initialBank :=
  let receipt := ControllerCappedSelected.selected_run sources p den hden k
    (PolynomialClock.ordinaryClock k) extra n x bits
  finalBank receipt.choose receipt.choose_spec.choose extra

/-- The entry is physically executed from the SAME capped admission bank.
Its fuel is the existing length-only envelope, not a supplied execution bound. -/
theorem ready_run
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) :
    ∃ B, Step (WorkspaceSelectedEntryReady.program sources p k r extra hspace).2
      (WorkspaceSelectedEntryBudget.envelope sources p k r n) (fun _ => 0)
      (initialBank sources p den hden k extra n x bits)
      (WorkspaceSelectedEntryReady.finalHeads sources p k r extra hspace) B := by
  let receipt := ControllerCappedSelected.selected_run sources p den hden k
    (PolynomialClock.ordinaryClock k) extra n x bits
  let A := receipt.choose
  let L := receipt.choose_spec.choose
  have hr := receipt.choose_spec.choose_spec.1
  have ho := OriginalHeaderRecovery.originals_of_run
    sources gamma p den hden k (PolynomialClock.ordinaryClock k) extra n x bits A L hr hp
  have hc := receipt.choose_spec.choose_spec.2.2.1 hp
  obtain ⟨oracle, _hdecode, hsize, w, out, run, _rest⟩ :=
    EntryRunFactoring.run_from_facts sources gamma p k r extra hspace n x bits A L ho hc
  exact ⟨_,run.enlarge (actual_fuel_le sources p den hden k r n x bits oracle hp hsize)⟩

def readyBank
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) :=
  Classical.choose (ready_run sources p den hden k r extra hspace n x bits hp)

theorem ready_step
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) :
    Step (WorkspaceSelectedEntryReady.program sources p k r extra hspace).2
      (WorkspaceSelectedEntryBudget.envelope sources p k r n) (fun _ => 0)
      (initialBank sources p den hden k extra n x bits)
      (WorkspaceSelectedEntryReady.finalHeads sources p k r extra hspace)
      (readyBank sources p den hden k r extra hspace n x bits hp) :=
  Classical.choose_spec (ready_run sources p den hden k r extra hspace n x bits hp)

end
end CappedEntryRun
