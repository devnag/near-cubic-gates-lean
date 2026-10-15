import Proof.MachineModel.TopDownWorkspaceSelectedEntryBudget
import Proof.MachineModel.TopDownSelectedRuntime

/-! Apply the selected-worker Runtime split with the actual entry initializer
paid once. The only remaining numeric execution bound is for the continuation
after entry, with its single residual-table term retained explicitly. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedEntryRuntime
open LocalBitMultitape RepairOrdinary RepairSource SourceInterfaces
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration
noncomputable section

def entryDegree (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) :=
  Classical.choose (WorkspaceSelectedEntryBudget.degree_before_hierarchy sources p)

def degree (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (remainingDegree : Nat) :=
  max (entryDegree sources p) remainingDegree

def fuel (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r : Nat) (remaining : Nat→Nat) (n : Nat) :=
  WorkspaceSelectedEntryBudget.envelope sources p k r n+1+remaining n

theorem entry_bound (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r : Nat) :
    ∃ coefficient onset,∀ n,onset≤n →
      WorkspaceSelectedEntryBudget.envelope sources p k r n≤coefficient*(n+1)^entryDegree sources p :=
  Classical.choose_spec (WorkspaceSelectedEntryBudget.degree_before_hierarchy sources p) k r

/-- The entry term is discharged here; the remaining inequality describes
the actual future clause/supplier/fold/tail execution and includes its bridge. -/
def of_remaining_bound {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    (C : SelectedAssembly.ContinuationData sources p) (r remainingDegree coefficient onset : Nat)
    (remaining : Nat→Nat) (tableCoefficient tableDegree : Nat)
    (hprogram : ∀n,C.fuel n≤fuel sources p C.k r remaining n)
    (hk : max (SelectedRuntime.prepDegree sources p) (degree sources p remainingDegree)≤C.k+1)
    (hremaining : ∀n,onset≤n → remaining n+3≤coefficient*(n+1)^remainingDegree+
      tableCoefficient*(2^(SelectedRuntime.width C n-(SelectedRuntime.sigma sources+tableDegree+2)*
        SelectedRuntime.logarithm C n)*(SelectedRuntime.width C n+1)^tableDegree)) :
    Runtime sources C.k C.clock
      (GuardedAssembly.workerData sources p (SelectedAssembly.programData C)).fuel := by
  let bound:=entry_bound sources p C.k r
  let E:=Classical.choose bound
  let cut:=Classical.choose (Classical.choose_spec bound)
  have hE:=Classical.choose_spec (Classical.choose_spec bound)
  apply SelectedRuntime.of_paper_body_bound C (degree sources p remainingDegree) (E+coefficient)
    (max cut onset) tableCoefficient tableDegree hk
  intro n hn
  have entry:=hE n ((Nat.le_max_left _ _).trans hn)
  change WorkspaceSelectedEntryBudget.envelope sources p C.k r n≤E*(n+1)^entryDegree sources p at entry
  have rest:=hremaining n ((Nat.le_max_right _ _).trans hn)
  have whole:=hprogram n
  have hp: (n+1)^entryDegree sources p≤(n+1)^degree sources p remainingDegree :=
    Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
  have hr: (n+1)^remainingDegree≤(n+1)^degree sources p remainingDegree :=
    Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)
  have ep:=Nat.mul_le_mul_left E hp
  have rp:=Nat.mul_le_mul_left coefficient hr
  unfold fuel at whole
  nlinarith

/-- Concrete hierarchy selection after admission, entry and continuation
degrees. Clock is canonical, and the entry fuel is the proven length-only
envelope of the actual EntryReady.run fuel. -/
def selected_runtime (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (r remainingDegree base extra : Nat) {states : Nat}
    (machine : Machine (WorkspaceSelectedAdmission.originalTapes sources p
      (SelectedRuntime.hierarchyIndex sources p (degree sources p remainingDegree))+1+1+extra) states)
    (result : Fin (WorkspaceSelectedAdmission.originalTapes sources p
      (SelectedRuntime.hierarchyIndex sources p (degree sources p remainingDegree))+1+1+extra))
    (remaining : Nat→Nat) (coefficient onset tableCoefficient tableDegree : Nat)
    (hremaining : let k:=SelectedRuntime.hierarchyIndex sources p (degree sources p remainingDegree)
      let C:=SelectedRuntime.continuation sources p (degree sources p remainingDegree) base extra machine result
        (fuel sources p k r remaining)
      ∀n,onset≤n → remaining n+3≤coefficient*(n+1)^remainingDegree+
        tableCoefficient*(2^(SelectedRuntime.width C n-(SelectedRuntime.sigma sources+tableDegree+2)*
          SelectedRuntime.logarithm C n)*(SelectedRuntime.width C n+1)^tableDegree)) :
    let k:=SelectedRuntime.hierarchyIndex sources p (degree sources p remainingDegree)
    let C:=SelectedRuntime.continuation sources p (degree sources p remainingDegree) base extra machine result
      (fuel sources p k r remaining)
    Runtime sources C.k C.clock
      (GuardedAssembly.workerData sources p (SelectedAssembly.programData C)).fuel := by
  intro k C
  exact of_remaining_bound C r remainingDegree coefficient onset remaining tableCoefficient tableDegree
    (fun _=>le_rfl) (SelectedRuntime.degrees_fit sources p (degree sources p remainingDegree)) hremaining

end
end NearCubicWires.P1TopDown.WorkspaceSelectedEntryRuntime
