import Proof.Amplification.RecoveryRowStructureFrontRun

/-! Physical updates of the retained parsed code and count cells. These
updates support the zero/singleton structural branches without changing the
witness cursor or the original row-kind word. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def setCode (d : Data) (bits : List Bool) : Data := {d with code:=bits}
def setCount (d : Data) (bits : List Bool) : Data := {d with count:=bits}

theorem right_code (d : Data) (bits : List Bool) :
    (setCode d bits).right=Function.update d.right 0 (frame bits) := by
  funext i
  fin_cases i <;> simp [setCode,Data.right]

theorem right_count (d : Data) (bits : List Bool) :
    (setCount d bits).right=Function.update d.right 1 (frame bits) := by
  funext i
  fin_cases i <;> simp [setCount,Data.right]

theorem cfg_code (d : Data) (capacity : Nat) (bits : List Bool) :
    (cfg (setCode d bits) capacity (0 : Fin 1)).tapes=
      Function.update (cfg d capacity (0 : Fin 1)).tapes 46 (frame bits) := by
  have hr : ((setCode d bits).cfg (0 : Fin 1)).tapes=
      Function.update (d.cfg (0 : Fin 1)).tapes 46 (frame bits) := by
    change Fin.addCases (m:=46) (n:=5) (motive:=fun _=>List Bool) d.left (setCode d bits).right=_
    rw [right_code,bank_update_right]
    rfl
  change Fin.addCases (m:=51) (n:=1) (motive:=fun _=>List Bool)
    ((setCode d bits).cfg (0 : Fin 1)).tapes (fun _=>List.replicate capacity false)=_
  rw [hr,bank_update_left]
  rfl

theorem cfg_count (d : Data) (capacity : Nat) (bits : List Bool) :
    (cfg (setCount d bits) capacity (0 : Fin 1)).tapes=
      Function.update (cfg d capacity (0 : Fin 1)).tapes 47 (frame bits) := by
  have hr : ((setCount d bits).cfg (0 : Fin 1)).tapes=
      Function.update (d.cfg (0 : Fin 1)).tapes 47 (frame bits) := by
    change Fin.addCases (m:=46) (n:=5) (motive:=fun _=>List Bool) d.left (setCount d bits).right=_
    rw [right_count,bank_update_right]
    rfl
  change Fin.addCases (m:=51) (n:=1) (motive:=fun _=>List Bool)
    ((setCount d bits).cfg (0 : Fin 1)).tapes (fun _=>List.replicate capacity false)=_
  rw [hr,bank_update_left]
  rfl

theorem setCode_valid (d : Data) (bits word : List Bool) (hd : d.Valid word)
    (hw : bits.length≤d.state.bits.length) : (setCode d bits).Valid word :=
  ⟨hd.1,hd.2.1,hd.2.2.1,hw,hd.2.2.2.2⟩

theorem setCount_valid (d : Data) (bits word : List Bool) (hd : d.Valid word)
    (hw : bits.length≤d.state.bits.length) : (setCount d bits).Valid word :=
  ⟨hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,hw⟩

def countClassified (d : Data) : Data :=
  setFlag (setFlag (setFlag (setCount d (RecoveryRowKind.after d.count))
    0 (decide (value d.count=0))) 1 (decide (value d.count=1))) 2 (decide (value d.count=2))

theorem countClassified_tapes (d : Data) (capacity : Nat) :
    (cfg (countClassified d) capacity (0 : Fin 1)).tapes=
      Function.update (Function.update (Function.update (Function.update (cfg d capacity (0 : Fin 1)).tapes
        47 (frame (RecoveryRowKind.after d.count))) 43 [decide (value d.count=0)])
          44 [decide (value d.count=1)]) 45 [decide (value d.count=2)] := by
  unfold countClassified
  rw [cfg_flag,cfg_flag,cfg_flag,cfg_count]
  rfl

theorem countClassified_valid (d : Data) (word : List Bool) (hd : d.Valid word) :
    (countClassified d).Valid word := by
  have hlen : (RecoveryRowKind.after d.count).length≤d.state.bits.length := by
    simpa [RecoveryRowKind.after,RecoveryLiteralTag.predWord] using hd.2.2.2.2
  exact setCount_valid d (RecoveryRowKind.after d.count) word hd hlen

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
