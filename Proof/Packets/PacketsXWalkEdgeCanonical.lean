import Proof.Packets.PacketsXWalkEdgeReuse

/-! The reusable edge keeps the two coordinates at fixed canonical ports.
The label changes the wiring of the worker, not the representation of its input. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option warningAsError true
namespace Theorem25Completion.WalkEdgeCanonical
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceInterfaces FixedLivePackets
noncomputable section

def slots (label : Fin 8) (i : Fin 7) : Fin 7:=
  if label.val<4 then i else if i=0 then 1 else if i=1 then 0 else i

theorem slots_involutive (label : Fin 8) : Function.Involutive (slots label) := by
  intro i
  by_cases hl : label.val<4
  · simp [slots,hl]
  · fin_cases i <;>simp [slots,hl]

theorem slots_injective (label : Fin 8) : Function.Injective (slots label):=
  (slots_involutive label).injective

def input (r R L : Nat) (v : MargulisVertex (2^r)) : Fin 7→List Bool:=
  ![WalkEdgeReuse.word r R v.1,WalkEdgeReuse.word r R v.2,List.replicate R false,
    List.replicate L false,List.replicate R true,UnaryTemplate.tape R,List.replicate (R+1) false]
def machine (label : Fin 8):=RecoveryFocus.machine (slots label) (WalkEdgeReuse.machine label)

theorem selected_heads (label : Fin 8) (i : Fin 7) :
    WalkEdgeReuse.heads i=WalkEdgeReuse.heads (slots label i) := by
  by_cases hl : label.val<4
  · simp [slots,hl]
  · fin_cases i <;>simp [slots,hl,WalkEdgeReuse.heads]

theorem selected_tapes (r R L : Nat) (label : Fin 8) (v : MargulisVertex (2^r)) (i : Fin 7) :
    WalkEdgeReuse.input r R L label v i=input r R L v (slots label i) := by
  by_cases hl : label.val<4
  all_goals fin_cases i <;>simp [WalkEdgeReuse.input,WalkEdgeReuse.bank,WalkEdgeReuse.extras,
    input,slots,hl,FinalWalkStep.active,FinalWalkStep.passive,Fin.addCases]

theorem run (r R L : Nat) (label : Fin 8) (v : MargulisVertex (2^r))
    (hR : 2*r+1≤R) (hL : 2*r+1≤L) :
    Step (machine label) (4*r+4*R+12) WalkEdgeReuse.heads (input r R L v)
      WalkEdgeReuse.heads (input r R L (margulisNeighbor label v)) := by
  apply PhysicalFocusBoundary.focus (WalkEdgeReuse.run r R L label v hR hL)
    (slots label) (slots_injective label) WalkEdgeReuse.heads WalkEdgeReuse.heads
    (input r R L v) (input r R L (margulisNeighbor label v))
  · exact selected_heads label
  · exact selected_tapes r R L label v
  · exact selected_heads label
  · exact selected_tapes r R L label (margulisNeighbor label v)
  · intro i away
    exact False.elim (away (slots label i) (slots_involutive label i))

end
end Theorem25Completion.WalkEdgeCanonical
