import Proof.MachineModel.OrdinaryWilliamsInputHeader

/-! A constant-size physical gate reads cells3 and5, retaining its source
and returning its head to zero. No prefix or payload is copied. -/
namespace NearCubicWires.RepairOrdinary.WilliamsZeroGate
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (state : Fin 16) (move : HeadMove) : Action 1 16 :=
  ⟨state,fun _ => none,fun _ => move⟩
def machine : Machine 1 16 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==10 || s.val==15
  rule := fun s bits =>
    ![some (action 1 .right),some (action 2 .right),some (action 3 .right),
      some (if bits 0 then action 8 .left else action 4 .right),some (action 5 .right),
      some (if bits 0 then action 6 .left else action 11 .left),
      some (action 7 .left),some (action 8 .left),some (action 9 .left),some (action 10 .left),none,
      some (action 12 .left),some (action 13 .left),some (action 14 .left),some (action 15 .left),none] s
def cfg (state : Fin 16) (pos : ℕ) (word : List Bool) : Configuration 1 16 :=
  ⟨state,fun _ => pos,fun _ => word⟩

theorem move_step (state next : Fin 16) (move : HeadMove) (pos : ℕ) (word : List Bool)
    (hr : machine.rule state (fun _ => readTapeBit word pos)=some (action next move)) :
    step machine (cfg state pos word)=some (cfg next (HeadMove.apply move pos) word) := by
  change Option.map (applyAction (cfg state pos word))
    (machine.rule state (fun _ => readTapeBit word pos))=some (cfg next (HeadMove.apply move pos) word)
  rw [hr]
  rfl

theorem front (word : List Bool) : Timed machine 3 (cfg 0 0 word) (cfg 3 3 word) := by
  exact Timed.step (by rfl) (move_step 0 1 .right 0 word (by rfl))
    (Timed.step (by rfl) (move_step 1 2 .right 1 word (by rfl))
      (Timed.step (by rfl) (move_step 2 3 .right 2 word (by rfl)) (Timed.refl _ _)))

theorem back_positive (word : List Bool) : Timed machine 4 (cfg 6 4 word) (cfg 10 0 word) := by
  exact Timed.step (by rfl) (move_step 6 7 .left 4 word (by rfl))
    (Timed.step (by rfl) (move_step 7 8 .left 3 word (by rfl))
      (Timed.step (by rfl) (move_step 8 9 .left 2 word (by rfl))
        (Timed.step (by rfl) (move_step 9 10 .left 1 word (by rfl)) (Timed.refl _ _))))
theorem back_zero (word : List Bool) : Timed machine 4 (cfg 11 4 word) (cfg 15 0 word) := by
  exact Timed.step (by rfl) (move_step 11 12 .left 4 word (by rfl))
    (Timed.step (by rfl) (move_step 12 13 .left 3 word (by rfl))
      (Timed.step (by rfl) (move_step 13 14 .left 2 word (by rfl))
        (Timed.step (by rfl) (move_step 14 15 .left 1 word (by rfl)) (Timed.refl _ _))))

theorem short_positive (word : List Bool) (h3 : readTapeBit word 3=true) :
    Timed machine 6 (cfg 0 0 word) (cfg 10 0 word) := by
  have hs : step machine (cfg 3 3 word)=some (cfg 8 2 word) :=
    move_step 3 8 .left 3 word (by simp [machine,h3])
  have ht := Timed.step (by rfl) hs
    (Timed.step (by rfl) (move_step 8 9 .left 2 word (by rfl))
      (Timed.step (by rfl) (move_step 9 10 .left 1 word (by rfl)) (Timed.refl _ _)))
  exact (front word).trans ht

theorem long_front (word : List Bool) (h3 : readTapeBit word 3=false) :
    Timed machine 5 (cfg 0 0 word) (cfg 5 5 word) := by
  have hs : step machine (cfg 3 3 word)=some (cfg 4 4 word) :=
    move_step 3 4 .right 3 word (by simp [machine,h3])
  exact (front word).trans (Timed.step (by rfl) hs
    (Timed.step (by rfl) (move_step 4 5 .right 4 word (by rfl)) (Timed.refl _ _)))

theorem long_positive (word : List Bool) (h3 : readTapeBit word 3=false) (h5 : readTapeBit word 5=true) :
    Timed machine 10 (cfg 0 0 word) (cfg 10 0 word) := by
  have hs : step machine (cfg 5 5 word)=some (cfg 6 4 word) :=
    move_step 5 6 .left 5 word (by simp [machine,h5])
  exact (long_front word h3).trans (Timed.step (by rfl) hs (back_positive word))
theorem long_zero (word : List Bool) (h3 : readTapeBit word 3=false) (h5 : readTapeBit word 5=false) :
    Timed machine 10 (cfg 0 0 word) (cfg 15 0 word) := by
  have hs : step machine (cfg 5 5 word)=some (cfg 11 4 word) :=
    move_step 5 11 .left 5 word (by simp [machine,h5])
  exact (long_front word h3).trans (Timed.step (by rfl) hs (back_zero word))

theorem total_run (word : List Bool) :
    ∃ r,run machine 10 (fun _ => word)=some r ∧ r.final.tapes=(fun _ => word) ∧
      (∀ i,r.final.heads i=0) ∧
      r.final.control=(if readTapeBit word 3 || readTapeBit word 5 then 10 else 15) ∧ r.steps ≤ 10 := by
  cases h3 : readTapeBit word 3 with
  | false =>
    cases h5 : readTapeBit word 5 with
    | false =>
      obtain ⟨r,hr,hf,hs⟩ := (long_zero word h3 h5).run (by rfl)
      exact ⟨r,hr,by simp [hf,cfg],by intro i; simp [hf,cfg],by simp [hf,cfg],hs.le⟩
    | true =>
      obtain ⟨r,hr,hf,hs⟩ := (long_positive word h3 h5).run (by rfl)
      exact ⟨r,hr,by simp [hf,cfg],by intro i; simp [hf,cfg],by simp [hf,cfg],hs.le⟩
  | true =>
    obtain ⟨r,hr,hf,hs⟩ := (short_positive word h3).run (by rfl)
    have hm := runFrom_moreFuel machine 6 4 _ r hr
    exact ⟨r,hm,by simp [hf,cfg],by intro i; simp [hf,cfg],by simp [hf,cfg],by omega⟩

end NearCubicWires.RepairOrdinary.WilliamsZeroGate
