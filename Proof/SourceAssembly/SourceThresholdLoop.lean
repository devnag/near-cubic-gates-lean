import Proof.SourceAssembly.SourceThresholdBody

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyThresholdLoop
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
noncomputable section

def cost (q : Nat):=4096*(q+1)^2
theorem body_cost (q j : Nat) (bits : List Bool) (hj : j≤q) (hlen : bits.length=q) :
    SourceAssemblyThresholdBody.budget q j bits≤cost q := by
  have hjb:=Natural.budget_fit q j hj
  have hn:natBitLength j≤j+1:=Nat.add_le_add_right (Nat.log_le_self 2 j) 1
  have hq:natBitLength q≤q+1:=Nat.add_le_add_right (Nat.log_le_self 2 q) 1
  simp only [SourceAssemblyThresholdBody.budget,
    SourceAssemblyThresholdIndex.budget,SourceAssemblyThresholdGate.budget,
    DecompositionSource.natWord_length,weights_length,hlen,cost,Capacity.value] at *
  nlinarith

def outputs (q : Nat) (bits : List Bool) (j : Nat) : Fin 2→List Bool:=
  fun i=>(List.range j).flatMap (fun k=>SourceAssemblyThresholdGate.emitted q k bits i)
theorem outputs_succ (q : Nat) (bits : List Bool) (j : Nat) :
    outputs q bits (j+1)=(fun i=>outputs q bits j i++SourceAssemblyThresholdGate.emitted q j bits i) := by
  funext i;simp [outputs,List.range_succ]

def machine:=CloseoutRowsDegreeLoop.machine SourceAssemblyThresholdBody.machine
def source {s : Nat} (p : Machine 32 s) (q : Nat) (bits : List Bool) (j : Nat) : Configuration 32 s:=
  ⟨p.start,SourceAssemblyThresholdBody.H (outputs q bits j),
    SourceAssemblyThresholdBody.A q j bits (outputs q bits j)⟩
def budget (q n : Nat):=n*(cost q+3)+3

theorem run (q n : Nat) (bits : List Bool) (hn : n≤q) (hlen : bits.length=q) :
    ∃ r,runFrom machine (budget q n)
      (RepeatMachine.cfg 0 (source SourceAssemblyThresholdBody.machine q bits 0) n 1)=some r ∧
      r.final=RepeatMachine.cfg 3 (source SourceAssemblyThresholdBody.machine q bits n) n 1 ∧
      r.steps≤budget q n := by
  apply CloseoutRowsDegreeLoop.loop_run SourceAssemblyThresholdBody.machine
    (fun j _=>source SourceAssemblyThresholdBody.machine q bits j) (fun _=>[])
    (cost q) n (by intro j hj out;rfl) _ []
  intro j hj out
  have h:=SourceAssemblyThresholdBody.run q j bits (outputs q bits j) (by omega) hlen
  rw [←outputs_succ] at h
  exact h.enlarge (body_cost q j bits (by omega) hlen)

end
end SourceAssemblyThresholdLoop
