import Proof.Packets.PacketsXWalkEdgeCanonical
import Proof.Packets.WalkBinaryDispatch
import Proof.Packets.FrozenWalkABI

/-! Four physical label bits select a reusable edge. The fourth bit is consumed
as part of the frozen sixteen-label alphabet, retaining its duplicated branches. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 15000
set_option warningAsError true
namespace Theorem25Completion.WalkLabelDispatch
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces NearCubicWires.SupplierWalk
noncomputable section

def branch (bits : List Bool) : Fin 8 := ⟨RadixSemantics.value bits%8,by omega⟩
def worker (bits : List Bool):=TapeEmbedding.machine 1 (WalkEdgeCanonical.machine (branch bits))
def machine:=WalkBinaryDispatch.machine worker (7 : Fin 8) 4 []
def heads (position : Nat) : Fin 8→Nat:=
  Fin.addCases (m:=7) (n:=1) (motive:=fun _=>Nat) WalkEdgeReuse.heads (fun _=>position)
def bank (r R L : Nat) (v : MargulisVertex (2^r)) (code : List Bool) : Fin 8→List Bool:=
  Fin.addCases (m:=7) (n:=1) (motive:=fun _=>List Bool)
    (WalkEdgeCanonical.input r R L v) (fun _=>code)

theorem branch_label (label : Fin 16) :
    branch (FrozenWalkABI.labelBits label)=duplicatedMargulisLabel label := by
  apply Fin.ext
  simp only [branch,FrozenWalkABI.labelBits_value]
  rfl

theorem advanced_heads (position amount : Nat) :
    WalkBinaryDispatch.advanced (7 : Fin 8) (heads position) amount=heads (position+amount) := by
  funext i
  fin_cases i <;>simp [heads,WalkBinaryDispatch.advanced,Fin.addCases]

theorem run (r R L : Nat) (label : Fin 16) (v : MargulisVertex (2^r))
    (pre tail : List Bool) (hR : 2*r+1≤R) (hL : 2*r+1≤L) :
    Step machine (4*r+4*R+28) (heads pre.length)
      (bank r R L v (pre++FrozenWalkABI.labelBits label++tail))
      (heads (pre.length+4))
      (bank r R L (duplicatedMargulisNeighbor label v) (pre++FrozenWalkABI.labelBits label++tail)) := by
  have hw:=((WalkEdgeCanonical.run r R L (duplicatedMargulisLabel label) v hR hL).embed
    (fun _ : Fin 1=>pre.length+4) (fun _=>pre++FrozenWalkABI.labelBits label++tail))
  have workerRun : Step (worker (FrozenWalkABI.labelBits label)) (4*r+4*R+12)
      (WalkBinaryDispatch.advanced (7 : Fin 8) (heads pre.length) (FrozenWalkABI.labelBits label).length)
      (bank r R L v (pre++FrozenWalkABI.labelBits label++tail))
      (heads (pre.length+4))
      (bank r R L (duplicatedMargulisNeighbor label v) (pre++FrozenWalkABI.labelBits label++tail)) := by
    rw [FrozenWalkABI.labelBits_length,advanced_heads]
    simpa only [worker,branch_label,heads,bank,duplicatedMargulisNeighbor] using hw
  have h:=WalkBinaryDispatch.run worker (7 : Fin 8) (FrozenWalkABI.labelBits label) [] pre tail
    (heads pre.length) (heads (pre.length+4)) _ _ rfl rfl workerRun
  rw [FrozenWalkABI.labelBits_length] at h
  exact h.enlarge (by omega)

end
end Theorem25Completion.WalkLabelDispatch
