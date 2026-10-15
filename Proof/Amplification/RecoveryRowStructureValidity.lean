import Proof.Amplification.RecoveryRowStructurePrepare
import Proof.Amplification.RecoveryRowStructureTagKind

/-! Actual one-step write of the streamed row's common success bit. This
result cell is reused by the structural front and the enclosing rejecting
row loop; the witness cursor and width driver retain their positions. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def setValid (d : Data) (bit : Bool) : Data := {d with valid:=bit}
def validMachine (bit : Bool) : Machine 52 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,fun i=>if i=50 then some bit else none,fun _=>.stay⟩ else none

theorem right_valid (d : Data) (bit : Bool) :
    (setValid d bit).right=Function.update d.right 4 [bit] := by
  funext i
  fin_cases i <;> simp [setValid,Data.right]

theorem row_valid (d : Data) (bit : Bool) :
    ((setValid d bit).cfg (0 : Fin 1)).tapes=Function.update (d.cfg (0 : Fin 1)).tapes 50 [bit] := by
  change Fin.addCases (m:=46) (n:=5) (motive:=fun _=>List Bool) d.left (setValid d bit).right=_
  rw [right_valid,bank_update_right]
  rfl

theorem cfg_valid (d : Data) (capacity : Nat) (bit : Bool) :
    (cfg (setValid d bit) capacity (0 : Fin 1)).tapes=
      Function.update (cfg d capacity (0 : Fin 1)).tapes 50 [bit] := by
  change Fin.addCases (m:=51) (n:=1) (motive:=fun _=>List Bool)
    ((setValid d bit).cfg (0 : Fin 1)).tapes (fun _=>List.replicate capacity false)=_
  rw [row_valid,bank_update_left]
  rfl

theorem valid_step (heads : Fin 52→Nat) (tapes : Fin 52→List Bool) (old bit : Bool)
    (hh : heads 50=0) (ht : tapes 50=[old]) :
    step (validMachine bit) (⟨0,heads,tapes⟩ : Configuration 52 2)=
      some (⟨1,heads,Function.update tapes 50 [bit]⟩ : Configuration 52 2) := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    by_cases hi : i=50
    · subst i
      simp [applyAction,hh,ht,writeTapeBit]
    · simp [applyAction,hi]

theorem valid_run (d : Data) (capacity : Nat) (bit : Bool) :
    ∃ r,runFrom (validMachine bit) 1 (cfg d capacity 0)=some r ∧
      r.final=cfg (setValid d bit) capacity 1 ∧ r.steps=1 := by
  have h := valid_step (cfg d capacity (0 : Fin 2)).heads (cfg d capacity (0 : Fin 2)).tapes d.valid bit (by rfl) (by rfl)
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) h).run (by rfl)
  refine ⟨r,hr,?_,hs⟩
  rw [hf]
  apply configuration_ext
  · rfl
  · rfl
  · exact (cfg_valid d capacity bit).symm

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
