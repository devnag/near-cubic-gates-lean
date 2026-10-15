import Proof.Hierarchy.CompetitorMonomialLoop

/-! Cold initialization for the bulk coefficient/count producer. The erase
reset counter and every arithmetic work tape begin blank and are generated
by the actual physical clear. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coldInput (b t : ℕ) (source : List Bool) : Fin 88 → List Bool := fun i =>
  if i.val=79 then source else if i.val=81 then List.replicate (width b) true
  else if i.val=82 then List.replicate (width t) true else if i.val=83 then List.replicate t true
  else if i.val=84 then List.replicate (capacity t) true else []
noncomputable def zeroed (b t : ℕ) (source : List Bool) : Fin 88 → List Bool :=
  install (extend workSlot) (coldInput b t source) (eraseInput (capacity t) (fun _ : Fin 81 => List.replicate (capacity t) false))

theorem extend_not_retained (j : Fin 83) (i : Fin 88)
    (hi : i=74 ∨ i=79 ∨ i=81 ∨ i=82 ∨ i=83) : extend workSlot j≠i := by
  rw [extend_cases]
  split
  · exact work_avoids _ i (by rcases hi with h|h|h|h|h <;> simp [h])
  · split
    · rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide
    · rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide

theorem cold_clear_run (b t : ℕ) (source : List Bool) :
    ClockJoin.ReadyRun (clearProgram workSlot) (2*capacity t+4) (coldInput b t source) (zeroed b t source) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := RecoveryScratchErase.erase_ready (capacity t) 0 (fun _ : Fin 81 => []) (by intro i; simp)
  have hi : Function.Injective (extend workSlot) := extend_injective workSlot work_injective
    (fun j => work_avoids j 84 (by simp)) (fun j => work_avoids j 85 (by simp))
  let start : Fin 83 → List Bool := Fin.addCases (m := 82) (n := 1) (motive := fun _ => List Bool)
    (Fin.addCases (m := 81) (n := 1) (motive := fun _ => List Bool)
      (fun _ => []) (fun _ => List.replicate (capacity t) true)) (fun _ => [])
  have ready : ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine 81) (2*capacity t+4) start
      (eraseInput (capacity t) (fun _ : Fin 81 => List.replicate (capacity t) false)) := by
    refine ⟨r,hr,?_,hh,hs.le⟩
    simpa only [eraseInput,Nat.zero_max,List.replicate_zero] using ht
  have hin : ∀ j,coldInput b t source (extend workSlot j)=start j := by intro j; fin_cases j <;> rfl
  exact CompetitorRationalProducts.bounded_focus (extend workSlot) hi _ _ _ ready (coldInput b t source) hin

theorem zeroed_store (b t : ℕ) (source : List Bool) : Store b t source [] (zeroed b t source) := by
  have hi : Function.Injective (extend workSlot) := extend_injective workSlot work_injective
    (fun j => work_avoids j 84 (by simp)) (fun j => work_avoids j 85 (by simp))
  have keep (i : Fin 88) (h : i=74 ∨ i=79 ∨ i=81 ∨ i=82 ∨ i=83) : zeroed b t source i=coldInput b t source i :=
    install_other (extend workSlot) _ _ i (fun j => extend_not_retained j i h)
  refine ⟨keep 79 (by simp),keep 74 (by simp),keep 81 (by simp),keep 82 (by simp),keep 83 (by simp),?_,?_,?_⟩
  · exact install_slot (extend workSlot) hi _ _ 81
  · exact install_slot (extend workSlot) hi _ _ 82
  · intro j
    have he := install_slot (extend workSlot) hi (coldInput b t source)
      (eraseInput (capacity t) (fun _ : Fin 81 => List.replicate (capacity t) false)) ((j.castAdd 1).castAdd 1)
    simp only [extend,eraseInput,Fin.addCases_left] at he
    change zeroed b t source (workSlot j)=List.replicate (capacity t) false at he
    rw [he,List.length_replicate]

end NearCubicWires.RepairOrdinary.CompetitorMonomialStream
