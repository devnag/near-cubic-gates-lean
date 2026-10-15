import Proof.MachineModel.ClockPreparation

/-! The fixed U rejects inputs shorter than two bits before numeric clock
preparation. This guard reads at most two framed bits and restores the head. -/
namespace NearCubicWires.RepairOrdinary.ClockSmallInput
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (state : Fin 7) (move : HeadMove) : Action 1 7 := ⟨state,fun _ => none,fun _ => move⟩
def machine : Machine 1 7 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==5 || s.val==6
  rule := fun s bits => if s.val=0 then some (if bits 0 then action 1 .right else action 5 .stay)
    else if s.val=1 then some (action 2 .right)
    else if s.val=2 then some (action (if bits 0 then 4 else 3) .left)
    else if s.val=3 then some (action 5 .left)
    else if s.val=4 then some (action 6 .left)
    else none

def cfg (state : Fin 7) (source : List Bool) (position : ℕ) : Configuration 1 7 :=
  ⟨state,fun _ => position,fun _ => source⟩

theorem guard_run (bits : List Bool) :
    ∃ r : ExecutionReceipt 1 7,
      run machine 4 (fun _ => frame bits)=some r ∧
      r.final=cfg (if 2≤bits.length then 6 else 5) (frame bits) 0 ∧ r.steps≤4 := by
  cases bits with
  | nil =>
    let r : ExecutionReceipt 1 7 := ⟨cfg 5 (frame []) 0,1,1⟩
    refine ⟨r,?_,rfl,by simp [r]⟩
    rfl
  | cons b bits =>
    cases bits with
    | nil =>
      let r : ExecutionReceipt 1 7 := ⟨cfg 5 (frame [b]) 0,4,3⟩
      refine ⟨r,?_,rfl,by simp [r]⟩
      simp [run,initialConfiguration,runFrom,machine,step,applyAction,action,
        Configuration.scanned,frame,readTapeBit,List.getD,HeadMove.apply,
        Configuration.tapeCells,r,cfg]
    | cons c bits =>
      let source := frame (b::c::bits)
      let r : ExecutionReceipt 1 7 := ⟨cfg 6 source 0,4,source.length⟩
      refine ⟨r,?_,rfl,by simp [r]⟩
      simp [run,initialConfiguration,runFrom,machine,step,applyAction,action,
        Configuration.scanned,source,frame,readTapeBit,List.getD,HeadMove.apply,
        Configuration.tapeCells,r,cfg]

end NearCubicWires.RepairOrdinary.ClockSmallInput
