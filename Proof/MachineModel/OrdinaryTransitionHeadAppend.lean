import Proof.MachineModel.OrdinaryTransitionEventRun

/-! Append one updated framed head to the next head array while retaining the
local head, width template and reset storage for the next tape event. -/
namespace NearCubicWires.RepairOrdinary.TransitionHeadAppend
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def close : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun i => if i.val=2 then some false else none,
      fun i => if i.val=2 then .right else .stay⟩ else none
def machine := Composition.machine KeyPrefix.machine close

theorem close_run (source template out : List Bool) (cap : ℕ) :
    ∃ r,runFrom close 1 (KeyPrefix.ready 0 source template out cap)=some r ∧
      r.final=KeyPrefix.ready 1 source template (out++[false]) cap := by
  have hs : step close (KeyPrefix.ready 0 source template out cap)=
      some (KeyPrefix.ready 1 source template (out++[false]) cap) := by
    simp [step,close,KeyPrefix.ready]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
    · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]
  obtain ⟨r,hr,hf,_⟩ := (Timed.single (by rfl : close.halted (0 : Fin 2)=false) hs).run (by rfl)
  exact ⟨r,hr,hf⟩

theorem append_run (bits template out : List Bool) (cap : ℕ)
    (hw : bits.length=template.length) (hc : 2*bits.length≤cap) :
    ∃ r,runFrom machine (4*bits.length+4)
      (KeyPrefix.ready 0 (frame bits) (frame template) out cap)=some r ∧
      r.final=KeyPrefix.ready 5 (frame bits) (frame template) (out++frame bits) cap := by
  obtain ⟨first,hfirst,hff,_,_⟩ := KeyPrefix.field_run bits [false] template out cap hw hc
  have he : Streaming.marks bits++[false]=frame bits := by
    simpa only [List.append_nil,frame] using (Streaming.frame_append bits []).symm
  rw [he] at hfirst hff
  obtain ⟨last,hlast,hlf⟩ := close_run (frame bits) (frame template) (out++Streaming.marks bits) cap
  have hmid : Composition.restart first.final close.start=
      KeyPrefix.ready 0 (frame bits) (frame template) (out++Streaming.marks bits) cap := by
    rw [hff]
    rfl
  rw [← hmid] at hlast
  have hj := Composition.run_join KeyPrefix.machine close (4*bits.length+2) 1
    (KeyPrefix.ready 0 (frame bits) (frame template) out cap) first last hfirst hlast
  have htime : (4*bits.length+2)+1+1=4*bits.length+4 := by omega
  rw [htime] at hj
  refine ⟨Composition.joinedReceipt first last,hj,?_⟩
  simp only [Composition.joinedReceipt,hlf,List.append_assoc,he]
  rfl

end NearCubicWires.RepairOrdinary.TransitionHeadAppend
