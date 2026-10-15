import Proof.Amplification.RecoveryRowStructureTagCalls

namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def setFlag (d : Data) (which : Fin 3) (bit : Bool) : Data :=
  {d with flags:=Function.update d.flags which bit}
def flagSlot (which : Fin 3) : Fin 52 := ⟨43+which.val,by omega⟩
def extraFlag (which : Fin 3) : Fin 4 := ⟨1+which.val,by omega⟩

theorem extra_flag (kind : List Bool) (flags : Fin 3→Bool) (which : Fin 3) (bit : Bool) :
    RecoveryRowLeaf.extra kind (Function.update flags which bit)=
      Function.update (RecoveryRowLeaf.extra kind flags) (extraFlag which) [bit] := by
  funext i
  fin_cases which <;> fin_cases i <;> simp [RecoveryRowLeaf.extra,extraFlag]

theorem left_flag (d : Data) (which : Fin 3) (bit : Bool) :
    (setFlag d which bit).left=Function.update d.left ((extraFlag which).natAdd 42) [bit] := by
  change Fin.addCases (m:=42) (n:=4) (motive:=fun _=>List Bool)
    (RecoveryClauseEvaluation.tapes d.state d.extra)
    (RecoveryRowLeaf.extra d.kind (Function.update d.flags which bit))=_
  rw [extra_flag,bank_update_right]
  rfl

theorem row_flag (d : Data) (which : Fin 3) (bit : Bool) :
    ((setFlag d which bit).cfg (0 : Fin 1)).tapes=
      Function.update (d.cfg (0 : Fin 1)).tapes (((extraFlag which).natAdd 42).castAdd 5) [bit] := by
  change Fin.addCases (m:=46) (n:=5) (motive:=fun _=>List Bool) (setFlag d which bit).left d.right=_
  rw [left_flag,bank_update_left]
  rfl

theorem cfg_flag (d : Data) (capacity : Nat) (which : Fin 3) (bit : Bool) :
    (cfg (setFlag d which bit) capacity (0 : Fin 1)).tapes=
      Function.update (cfg d capacity (0 : Fin 1)).tapes (flagSlot which) [bit] := by
  change Fin.addCases (m:=51) (n:=1) (motive:=fun _=>List Bool)
    ((setFlag d which bit).cfg (0 : Fin 1)).tapes (fun _=>List.replicate capacity false)=_
  rw [row_flag,bank_update_left]
  congr 1
  apply Fin.ext
  simp only [extraFlag,flagSlot,Fin.val_castAdd,Fin.val_natAdd]
  omega

theorem setFlag_valid (d : Data) (which : Fin 3) (bit : Bool) (word : List Bool)
    (hd : d.Valid word) : (setFlag d which bit).Valid word := hd

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
