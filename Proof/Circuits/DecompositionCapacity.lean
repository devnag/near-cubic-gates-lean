import Proof.Circuits.DecompositionCapacityBoot

/-! Actual cold capacity from the original framed native payload. The fixed
one-field count is written, then the existing measured-byte power producer
runs. Coefficient and degree stay abstract throughout this composition. -/
namespace NearCubicWires.RepairOrdinary.DecompositionCapacity
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine (D C : ℕ) := Composition.machine (boot D) (PCPSerializerCapacity.machine D C)
def budget (D C N : ℕ) := 3+PCPSerializerCapacity.budget D C N

theorem capacity_cold (D C : ℕ) (payload : List Bool) :
    ∃ r,run (machine D C) (budget D C (frame payload).length)
      (input D (frame payload) [])=some r ∧
      r.final.heads=PCPSerializerCapacity.heads D 0 ∧
      r.final.tapes (PCPSerializerCapacity.old D 0)=frame payload ∧
      r.final.tapes (PCPSerializerCapacity.old D 1)=List.replicate (frame payload).length true ∧
      r.final.tapes (PCPSerializerCapacity.capacitySlot D)=
        List.replicate (C*((frame payload).length+1)^D) true ∧
      r.steps ≤ budget D C (frame payload).length := by
  obtain ⟨first,hfirst,ff,fs⟩ := boot_run D (frame payload)
  obtain ⟨last,hl,ls,lh,l0,_,l1,lC⟩ := PCPSerializerCapacity.capacity_run D C [] [payload] []
  have he : RepairSource.ProjectionNormalization.FieldList.stream [payload]=frame payload := by
    simp [RepairSource.ProjectionNormalization.FieldList.stream]
  simp only [he,List.length_singleton,List.length_nil,List.nil_append,List.append_nil] at hl l0 l1 lC lh ls
  have hr : Composition.restart first.final (PCPSerializerCapacity.machine D C).start=
      PCPSerializerCapacity.entry D (PCPSerializerCapacity.machine D C).start (frame payload) 0 1 := by
    rw [ff]
    rfl
  rw [←hr] at hl
  have joined := Composition.run_join (boot D) (PCPSerializerCapacity.machine D C)
    _ _ _ first last hfirst hl
  refine ⟨Composition.joinedReceipt first last,joined,lh,l0,l1,lC,?_⟩
  change first.steps+1+last.steps ≤ _
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.DecompositionCapacity
