import Proof.Packets.PacketsXWalkEdgeReady
import Proof.Packets.PhysicalCopyInto
import Proof.Packets.CycleFieldPrimitives

/-! Reusable seven-tape Margulis edge: execute the arithmetic sweep, copy
the new coordinate over the old one, and physically clear the temporary word. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
namespace Theorem25Completion.WalkEdgeReuse
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceInterfaces FixedLivePackets
open FixedLivePackets.Materializer
noncomputable section

def word (r R : Nat) (a : ZMod (2^r)):=ZeroPadding.pad R (frame (FinalWalkStep.coordEncode r a))
def extras (R : Nat) : Fin 3→List Bool:=
  ![List.replicate R true,UnaryTemplate.tape R,List.replicate (R+1) false]
def bank (r R L : Nat) (label : Fin 8) (v : MargulisVertex (2^r)) (tmp : List Bool) : Fin 7→List Bool:=
  Fin.addCases (m:=4) (n:=3) (motive:=fun _=>List Bool)
    (![word r R (FinalWalkStep.active label v),word r R (FinalWalkStep.passive label v),
      tmp,List.replicate L false]) (extras R)
def input (r R L : Nat) (label : Fin 8) (v : MargulisVertex (2^r)):=
  bank r R L label v (List.replicate R false)
def middle (r R L : Nat) (label : Fin 8) (v : MargulisVertex (2^r)):=
  bank r R L label v (word r R (FinalWalkStep.active label (margulisNeighbor label v)))
def heads (i : Fin 7) : Nat:=if i=5 then 1 else 0
def clearSlots : Fin 3→Fin 7:=![2,4,6]
def edge (label : Fin 8):=TapeEmbedding.machine 3 (WalkEdgeReady.machine label)
def copy:=PhysicalCopyInto.machine (5 : Fin 7) 2 0
def clear:=RecoveryFocus.machine clearSlots (CycleFields.Primitives.eraseMachine 1)
def machine (label : Fin 8):=Composition.machine (Composition.machine (edge label) copy) clear

theorem word_length (r R : Nat) (a : ZMod (2^r)) (hR : 2*r+1≤R) :
    (word r R a).length=R := by
  simp [word,ZeroPadding.pad_length,frame_length,FinalWalkStep.coordEncode_length,Nat.max_eq_left hR]

theorem edge_run (r R L : Nat) (label : Fin 8) (v : MargulisVertex (2^r)) (hL : 2*r+1≤L) :
    Step (edge label) (4*r+4) heads (input r R L label v) heads (middle r R L label v) := by
  let caps : Fin 4→Nat:=![R,R,R,L]
  have h:=((WalkEdgeReady.run r L label v hL).pad caps).embed
    (![0,1,0] : Fin 3→Nat) (extras R)
  have hh : (Fin.addCases (m:=4) (n:=3) (motive:=fun _=>Nat)
      (fun _=>0) (![0,1,0]))=heads := by funext i;fin_cases i <;>rfl
  have hi : (Fin.addCases (m:=4) (n:=3) (motive:=fun _=>List Bool)
      (fun i=>ZeroPadding.pad (caps i) (WalkEdgeReady.input r L label v i)) (extras R))=
      input r R L label v := by
    funext i;fin_cases i
    all_goals first | rfl | simp [caps,WalkEdgeReady.input,
      input,bank,Fin.addCases,ZeroPadding.pad]
  have ho : (Fin.addCases (m:=4) (n:=3) (motive:=fun _=>List Bool)
      (fun i=>ZeroPadding.pad (caps i) (WalkEdgeReady.output r L label v i)) (extras R))=
      middle r R L label v := by
    funext i;fin_cases i
    all_goals first | rfl | simp [caps,WalkEdgeReady.output,
      middle,bank,Fin.addCases,ZeroPadding.pad]
  exact (h.congr_in hh hi).congr hh ho

theorem run (r R L : Nat) (label : Fin 8) (v : MargulisVertex (2^r))
    (hR : 2*r+1≤R) (hL : 2*r+1≤L) :
    Step (machine label) (4*r+4*R+12) heads (input r R L label v)
      heads (input r R L label (margulisNeighbor label v)) := by
  let M:=middle r R L label v
  have copyRun:=PhysicalCopyInto.run R (5 : Fin 7) 2 0 (by decide) (by decide) (by decide)
    heads M (by rfl) (by rfl) (by rfl) (by rfl)
    (word_length r R _ hR) (word_length r R _ hR)
  let afterCopy:=Function.update M (0 : Fin 7) (M 2)
  have eraseRun:=CycleFields.Primitives.erase_step R (R+1) (fun _ : Fin 1=>M 2)
    (by intro i;exact (word_length r R _ hR).le) le_rfl
  have clearRun : Step clear (2*R+4) heads afterCopy heads
      (input r R L label (margulisNeighbor label v)) := by
    apply PhysicalFocusBoundary.focus eraseRun clearSlots (by decide) heads heads
      afterCopy (input r R L label (margulisNeighbor label v))
    · intro i;fin_cases i <;>rfl
    · intro i;fin_cases i <;>rfl
    · intro i;fin_cases i <;>rfl
    · intro i;fin_cases i <;>rfl
    · intro i away
      refine ⟨rfl,?_⟩
      fin_cases i
      · rfl
      · change word r R (FinalWalkStep.passive label v)=
          word r R (FinalWalkStep.passive label (margulisNeighbor label v))
        rw [FinalWalkStep.passive_neighbor]
      · exact False.elim (away 0 rfl)
      · rfl
      · exact False.elim (away 1 rfl)
      · rfl
      · exact False.elim (away 2 rfl)
  have h:=((edge_run r R L label v hL).seq copyRun).seq clearRun
  exact h.enlarge (by omega)

end
end Theorem25Completion.WalkEdgeReuse
