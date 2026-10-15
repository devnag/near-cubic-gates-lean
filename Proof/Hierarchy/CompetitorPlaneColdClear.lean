import Proof.Hierarchy.CompetitorPlaneLoop

/-! Cold plane entry: all arithmetic and reset work tapes start blank.
The first actual erase creates the complete reusable workspace. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlaneStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorPlaneWorkspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coldInput (b w : ℕ) (bits counts old : List Bool) : Fin 27 → List Bool := fun i =>
  if i.val=0 then frame bits else if i.val=9 then List.replicate w true
  else if i.val=18 then counts else if i.val=19 then old
  else if i.val=20 then List.replicate b true else if i.val=21 then List.replicate (CompetitorPlane.capacity w) true else []
noncomputable def zeroed (b w : ℕ) (bits counts old : List Bool) : Fin 27 → List Bool :=
  install (extend workSlot) (coldInput b w bits counts old)
    (eraseInput (CompetitorPlane.capacity w) (fun _ : Fin 19 => List.replicate (CompetitorPlane.capacity w) false))

theorem extend_not_retained (j : Fin 21) (i : Fin 27)
    (hi : i=0 ∨ i=9 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20) : extend workSlot j≠i := by
  rw [extend_cases]
  split
  · apply work_avoids
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> simp [retainedSlot]
  · split
    · rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    · rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem cold_clear_run (b w : ℕ) (bits counts old : List Bool) :
    ClockJoin.ReadyRun (clearProgram workSlot) (2*CompetitorPlane.capacity w+4)
      (coldInput b w bits counts old) (zeroed b w bits counts old) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := RecoveryScratchErase.erase_ready (CompetitorPlane.capacity w) 0 (fun _ : Fin 19 => []) (by intro i; simp)
  have hi : Function.Injective (extend workSlot) := extend_injective workSlot work_injective
    (fun j => work_avoids j 21 (by simp [retainedSlot])) (fun j => work_avoids j 22 (by simp [retainedSlot]))
  let start : Fin 21 → List Bool := Fin.addCases (m := 20) (n := 1) (motive := fun _ => List Bool)
    (Fin.addCases (m := 19) (n := 1) (motive := fun _ => List Bool)
      (fun _ => []) (fun _ => List.replicate (CompetitorPlane.capacity w) true)) (fun _ => [])
  have ready : ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine 19) (2*CompetitorPlane.capacity w+4) start
      (eraseInput (CompetitorPlane.capacity w) (fun _ : Fin 19 => List.replicate (CompetitorPlane.capacity w) false)) := by
    refine ⟨r,hr,?_,hh,hs.le⟩
    simpa only [eraseInput,Nat.zero_max,List.replicate_zero] using ht
  have hin : ∀ j,coldInput b w bits counts old (extend workSlot j)=start j := by intro j; fin_cases j <;> rfl
  exact CompetitorRationalProducts.bounded_focus (extend workSlot) hi _ _ _ ready (coldInput b w bits counts old) hin

theorem zeroed_store (b w : ℕ) (bits counts old : List Bool) :
    Store b w bits counts old [] (zeroed b w bits counts old) := by
  have hi : Function.Injective (extend workSlot) := extend_injective workSlot work_injective
    (fun j => work_avoids j 21 (by simp [retainedSlot])) (fun j => work_avoids j 22 (by simp [retainedSlot]))
  have keep (i : Fin 27) (h : i=0 ∨ i=9 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20) :
      zeroed b w bits counts old i=coldInput b w bits counts old i :=
    install_other (extend workSlot) _ _ i (fun j => extend_not_retained j i h)
  refine ⟨keep 0 (by simp),keep 9 (by simp),keep 17 (by simp),keep 18 (by simp),keep 19 (by simp),keep 20 (by simp),?_,?_,?_⟩
  · exact install_slot (extend workSlot) hi _ _ 19
  · exact install_slot (extend workSlot) hi _ _ 20
  · intro j
    have he := install_slot (extend workSlot) hi (coldInput b w bits counts old)
      (eraseInput (CompetitorPlane.capacity w) (fun _ : Fin 19 => List.replicate (CompetitorPlane.capacity w) false))
      ((j.castAdd 1).castAdd 1)
    simp only [extend,eraseInput,Fin.addCases_left] at he
    change zeroed b w bits counts old (workSlot j)=List.replicate (CompetitorPlane.capacity w) false at he
    rw [he,List.length_replicate]

end NearCubicWires.RepairOrdinary.CompetitorPlaneStream
