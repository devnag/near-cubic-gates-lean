import Proof.MachineModel.TopDownWorkspaceSelectedProgram

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.SelectedAssembly
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource RepairSource.CloseoutFinal SourceInterfaces
open RepairSource.CloseoutFinal.C10GuardedMachineConsumer
noncomputable section
attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes

structure ContinuationData (sources : EightSources) {gamma : Real}
    (p : Parameters sources gamma) where
  k : Nat
  clock : OrdinaryClock (fun n => n^(k+2))
  base : Nat
  extra : Nat
  states : Nat
  machine : LocalBitMultitape.Machine (WorkspaceSelectedAdmission.originalTapes sources p k+1+1+extra) states
  result : Fin (WorkspaceSelectedAdmission.originalTapes sources p k+1+1+extra)
  fuel : Nat → Nat

def programData {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    (C : ContinuationData sources p) : GuardedAssembly.ProgramData :=
  WorkspaceSelectedProgram.programData sources p C.k C.clock C.base C.extra C.machine C.result C.fuel

structure Remaining {sources : EightSources} {gamma : Real} (p : Parameters sources gamma)
    (C : ContinuationData sources p) : Type 1 where
  admitted : ∀ n x bits, (GuardedAssembly.workerData sources p (programData C)).onset≤n →
    (GuardedAssembly.workerData sources p (programData C)).passed n x bits=true →
    DecodedVerdictAt sources p (GuardedAssembly.workerData sources p (programData C))
      (by change 2≤WorkspaceSelectedAdmission.originalTapes sources p C.k+1+1+C.extra; omega) n x bits
  runtime : Runtime sources C.k C.clock (GuardedAssembly.workerData sources p (programData C)).fuel

def obligations {sources : EightSources} {gamma : Real} (p : Parameters sources gamma)
    (C : ContinuationData sources p) (R : Remaining p C) :
    GuardedAssembly.Obligations sources p (programData C) where
  htapes := by change 2≤WorkspaceSelectedAdmission.originalTapes sources p C.k+1+1+C.extra; omega
  hinput := rfl
  hflag := by
    intro h
    have hv := congrArg Fin.val h
    change WorkspaceSelectedAdmission.originalTapes sources p C.k+1=0 at hv
    omega
  admission_run := WorkspaceSelectedProgram.admission_run sources p C.k C.clock C.base C.extra
    C.machine C.result C.fuel
  admitted := R.admitted
  runtime := R.runtime

theorem close
    (choose : (sources : EightSources) → ∀ gamma : Real, 0<gamma → gamma<1/2 →
      (p : Parameters sources gamma) → ContinuationData sources p)
    (construct : (sources : EightSources) → ∀ gamma : Real, ∀ hg : 0<gamma,
      ∀ hh : gamma<1/2, (p : Parameters sources gamma) →
      Remaining p (choose sources gamma hg hh p)) :
    EightSources → OrdinaryHeadlineTheorem25 := by
  exact GuardedAssembly.close
    (fun sources gamma hg hh p => programData (choose sources gamma hg hh p))
    (fun sources gamma hg hh p => obligations p (choose sources gamma hg hh p)
      (construct sources gamma hg hh p))

end
end NearCubicWires.P1TopDown.SelectedAssembly
