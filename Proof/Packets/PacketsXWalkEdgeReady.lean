import Proof.Rows.FinalWalkStep
import Proof.MachineModel.Runs

/-! One actual Margulis edge with a reusable rewind reserve. All four
cursors return to zero, and both source coordinates are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace Theorem25Completion.WalkEdgeReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces
open NearCubicWires.RepairOrdinary.RecoveryRootRound

def machine (label : Fin 8):=MaskedReset.machine
  (FinalWalkStep.machine (FinalWalkStep.labelInvert label) (FinalWalkStep.labelCarry label)) (fun _=>true)
def input (r L : Nat) (label : Fin 8) (v : MargulisVertex (2^r)) : Fin 4→List Bool:=
  Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool)
    (FinalWalkStep.loadTapes r label v) (fun _ : Fin 1=>List.replicate L false)
def result (r : Nat) (label : Fin 8) (v : MargulisVertex (2^r)) : Fin 3→List Bool:=
  ![frame (FinalWalkStep.coordEncode r (FinalWalkStep.active label v)),
    frame (FinalWalkStep.coordEncode r (FinalWalkStep.passive label v)),
    frame (FinalWalkStep.coordEncode r (FinalWalkStep.active label (margulisNeighbor label v)))]
def output (r L : Nat) (label : Fin 8) (v : MargulisVertex (2^r)) : Fin 4→List Bool:=
  Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool)
    (result r label v) (fun _ : Fin 1=>List.replicate L false)

theorem run (r L : Nat) (label : Fin 8) (v : MargulisVertex (2^r)) (hL : 2*r+1≤L) :
    Step (machine label) (4*r+4) (fun _=>0) (input r L label v)
      (fun _=>0) (output r L label v) := by
  obtain ⟨rec,hr,hs,h0,h1,h2⟩:=FinalWalkStep.walk_step_run r label v
  have ht : rec.final.tapes=result r label v := by
    funext i
    fin_cases i
    · exact h0
    · rw [FinalWalkStep.passive_neighbor] at h1
      exact h1
    · exact h2
  have raw : Step (FinalWalkStep.machine (FinalWalkStep.labelInvert label) (FinalWalkStep.labelCarry label))
      (2*r+1) (fun _=>0) (FinalWalkStep.loadTapes r label v) rec.final.heads (result r label v) :=
    ⟨rec,hr,rfl,ht,hs.le⟩
  have ready:=raw.mask (fun _=>true) (by intro i hi;rfl) hL
  have hz : (Fin.addCases (m:=3) (n:=1) (motive:=fun _=>Nat)
      (fun _=>0) (fun _=>0))=(fun _ : Fin 4=>0) := by
    funext i;fin_cases i <;>rfl
  have hb : 2*(2*r+1)+2=4*r+4:=by omega
  simp only [↓reduceIte,hz,hb] at ready
  exact ready

end Theorem25Completion.WalkEdgeReady
