import Proof.Packets.PacketsXWalkLabelDispatch
import Proof.Packets.PacketsXWalkPoweredWord

/-! A fixed forty-edge physical program realizes the frozen powered Margulis
transition. Its entire label word is read from tape and retained. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 20000
set_option warningAsError true
namespace Theorem25Completion.WalkPoweredRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces NearCubicWires.SupplierWalk
noncomputable section

def idle : Machine 8 1:=⟨0,0,fun _=>true,fun _ _=>none⟩
def stateCount {t s : Nat} (_ : Machine t s) : Nat:=s
def states : Nat→Nat
  | 0=>1
  | n+1=>stateCount WalkLabelDispatch.machine+states n
def repeated : (n : Nat)→Machine 8 (states n)
  | 0=>idle
  | n+1=>Composition.machine WalkLabelDispatch.machine (repeated n)

theorem idle_run (H : Fin 8→Nat) (A : Fin 8→List Bool) : Step idle 0 H A H A := by
  let cfg : Configuration 8 1:=⟨0,H,A⟩
  exact ⟨⟨cfg,0,cfg.tapeCells⟩,rfl,rfl,rfl,le_rfl⟩

theorem repeated_run {n : Nat} (r R L : Nat) (labels : Fin n→Fin 16)
    (v : MargulisVertex (2^r)) (pre tail : List Bool)
    (hR : 2*r+1≤R) (hL : 2*r+1≤L) :
    Step (repeated n) (n*(4*r+4*R+29)) (WalkLabelDispatch.heads pre.length)
      (WalkLabelDispatch.bank r R L v (pre++WalkPoweredWord.word labels++tail))
      (WalkLabelDispatch.heads (pre.length+4*n))
      (WalkLabelDispatch.bank r R L (tupleWalk duplicatedMargulisNeighbor labels v)
        (pre++WalkPoweredWord.word labels++tail)) := by
  induction n generalizing v pre with
  | zero=>
    simpa only [repeated,states,tupleWalk,Nat.mul_zero,Nat.zero_mul,Nat.add_zero] using
      (idle_run (WalkLabelDispatch.heads pre.length)
        (WalkLabelDispatch.bank r R L v (pre++WalkPoweredWord.word labels++tail)))
  | succ n ih=>
    have first:=WalkLabelDispatch.run r R L (labels 0) v pre
      (WalkPoweredWord.word (Fin.tail labels)++tail) hR hL
    simp only [List.append_assoc] at first
    have rest:=ih (Fin.tail labels) (duplicatedMargulisNeighbor (labels 0) v)
      (pre++FrozenWalkABI.labelBits (labels 0))
    simp only [List.length_append,FrozenWalkABI.labelBits_length,List.append_assoc] at rest
    have h:=first.seq rest
    have hh : pre.length+4+4*n=pre.length+4*(n+1) := by omega
    rw [hh] at h
    have converted : Step (repeated (n+1))
        ((4*r+4*R+28)+1+n*(4*r+4*R+29)) (WalkLabelDispatch.heads pre.length)
        (WalkLabelDispatch.bank r R L v (pre++WalkPoweredWord.word labels++tail))
        (WalkLabelDispatch.heads (pre.length+4*(n+1)))
        (WalkLabelDispatch.bank r R L (tupleWalk duplicatedMargulisNeighbor labels v)
          (pre++WalkPoweredWord.word labels++tail)) := by
      simpa only [repeated,states,stateCount,WalkPoweredWord.word,tupleWalk,List.append_assoc] using h
    exact converted.enlarge (by nlinarith)

def machine:=repeated 40

theorem run (r R L : Nat) (label : PoweredMargulisLabel) (v : MargulisVertex (2^r))
    (pre tail : List Bool) (hR : 2*r+1≤R) (hL : 2*r+1≤L) :
    Step machine (160*r+160*R+1160) (WalkLabelDispatch.heads pre.length)
      (WalkLabelDispatch.bank r R L v (pre++WalkPoweredWord.word label++tail))
      (WalkLabelDispatch.heads (pre.length+160))
      (WalkLabelDispatch.bank r R L (poweredMargulisNeighbor label v)
        (pre++WalkPoweredWord.word label++tail)) := by
  exact (repeated_run r R L label v pre tail hR hL).enlarge (by omega)

end
end Theorem25Completion.WalkPoweredRun
