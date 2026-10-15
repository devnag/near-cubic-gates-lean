import Proof.Amplification.RecoveryRawLiteralBoundCompare

/-! The bound inspector's actual stream, comparison and accumulation calls
retain all unrelated tapes and the physical witness cursor. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawLiteralBound
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem mark_run (x : State) :
    ∃ r,runFrom markMachine 1 (x.cfg markMachine.start)=some r ∧
      r.final=(marked x).cfg r.final.control ∧ r.steps=1 := by
  have h : step markMachine (x.cfg 0)=some ((marked x).cfg 1) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) h).run (by rfl)
  refine ⟨r,hr,?_,hs⟩
  rw [hf]
  rfl

theorem check_run (x : State) (index : List Bool)
    (hf : x.stream.data.data.fields 0=frame index)
    (hw : x.bound.length=index.length)
    (hc : 2*x.bound.length+3 ≤ x.stream.data.data.capacity) :
    ∃ r,runFrom checkMachine (4*x.bound.length+8+1+1) (x.cfg checkMachine.start)=some r ∧
      r.final=(marked (compared x index)).cfg r.final.control ∧ r.steps=4*x.bound.length+8+1+1 := by
  obtain ⟨first,hr0,hf0,hs0⟩ := compare_run x index hf hw hc
  obtain ⟨last,hr1,hf1,hs1⟩ := mark_run (compared x index)
  have he : Composition.restart first.final markMachine.start=(compared x index).cfg markMachine.start := by rw [hf0]; rfl
  rw [←he] at hr1
  have hr := Composition.run_join compareMachine markMachine (4*x.bound.length+8) 1 _ first last hr0 hr1
  refine ⟨Composition.joinedReceipt first last,hr,?_,?_⟩
  · apply configuration_ext
    · rfl
    · change last.final.heads=_; rw [hf1]; rfl
    · change last.final.tapes=_; rw [hf1]; rfl
  · change first.steps+1+last.steps=_
    rw [hs0,hs1]

theorem stream_run (x : State) (hx : x.Valid) :
    ∃ r,runFrom streamMachine (RecoveryRawLiteralStream.cost x.stream) (x.cfg streamMachine.start)=some r ∧
      r.final=(decoded x).cfg r.final.control ∧ r.steps ≤ RecoveryRawLiteralStream.cost x.stream := by
  obtain ⟨base,hr,hf,hb⟩ := RecoveryRawLiteralStream.stream_run x.stream hx.1
  have h := TapeEmbedding.run_embed RecoveryRawLiteralStream.machine
    (fun _ : Fin 4=>0) x.extra (RecoveryRawLiteralStream.cost x.stream)
    (x.stream.cfg RecoveryRawLiteralStream.machine.start) base hr
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 4=>0) x.extra base,h,?_,hb⟩
  change TapeEmbedding.config (fun _ : Fin 4=>0) x.extra base.final=_
  rw [hf]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryRawLiteralBound
