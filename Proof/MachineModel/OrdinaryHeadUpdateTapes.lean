import Proof.Amplification.RecoveryReadyCalls
import Proof.MachineModel.OrdinaryWitnessCounterAdvance

/-! Exact retained-tape contracts for the control walk's head update. The
ordinary compare, subtract, copy and increment programs are reused. -/
namespace NearCubicWires.RepairOrdinary.HeadUpdate
open LocalBitMultitape SignedSortKey RadixSemantics RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Store where
  head : ℕ
  difference : List Bool
  flag : Bool
  move : HeadMove

def low : HeadMove → Bool | .left => false | .stay => true | .right => false
def high : HeadMove → Bool | .left => false | .stay => false | .right => true
def Store.tapes (s : Store) (w cap : ℕ) : Fin 8 → List Bool :=
  ![frame (binary w s.head),frame (binary w 1),s.difference,[s.flag],
    List.replicate cap false,List.replicate cap false,[low s.move],[high s.move]]
def cleared (s : Store) : Store := {s with flag := false}
def compared (s : Store) : Store := {s with flag := decide (1 ≤ s.head)}
def subtracted (s : Store) (w : ℕ) : Store :=
  {s with difference := frame (binary w (s.head-1))}
def copied (s : Store) : Store := {s with head := s.head-1}
def incremented (s : Store) : Store := {s with head := s.head+1}

def clearMachine : Machine 8 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then
    some ⟨1,fun i => if i.val = 3 then some false else none,fun _ => .stay⟩ else none

theorem clear_ready (s : Store) (w cap : ℕ) :
    ReadyRun clearMachine 1 (s.tapes w cap) ((cleared s).tapes w cap) := by
  have hs : step clearMachine (initialConfiguration clearMachine (s.tapes w cap)) =
      some (⟨1,fun _ => 0,(cleared s).tapes w cap⟩ : Configuration 8 2) := by
    simp [step,clearMachine,initialConfiguration]
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [applyAction,Store.tapes,cleared,writeTapeBit]
  have hp := Timed.single (by rfl : clearMachine.halted clearMachine.start=false) hs
  obtain ⟨r,hr,hf,ht⟩ := hp.run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i; rw [hf],ht⟩

def compareSlots : Fin 4 → Fin 8 := ![1,0,3,4]
def subtractSlots : Fin 4 → Fin 8 := ![0,1,2,4]
def copySlots : Fin 4 → Fin 8 := ![2,0,5,4]
def incrementSlots : Fin 2 → Fin 8 := ![0,4]

noncomputable def compareProgram := RecoveryFocus.machine compareSlots compareMachine
noncomputable def subtractProgram := RecoveryFocus.machine subtractSlots subtractMachine
noncomputable def copyProgram := RecoveryFocus.machine copySlots copyMachine
noncomputable def incrementProgram := RecoveryFocus.machine incrementSlots FramedIncrement.machine

theorem compare_layout (s : Store) (w cap : ℕ) (ha : s.head<2^w) (hw : 1<2^w)
    (hc : 2*w+1≤cap) :
    ReadyRun compareProgram (4*w+4) ((cleared s).tapes w cap) ((compared s).tapes w cap) := by
  have h := compare_ready (binary w 1) (binary w s.head) cap (by simp)
  simp only [binary_length,binary_value _ _ hw,binary_value _ _ ha,max_eq_left hc] at h
  have hr := h.focus compareSlots (by decide) ((cleared s).tapes w cap)
    (by intro j; fin_cases j <;> rfl)
  have he : install compareSlots ((cleared s).tapes w cap)
      (![frame (binary w 1),frame (binary w s.head),[decide (1 ≤ s.head)],
        List.replicate cap false] : Fin 4 → List Bool) = (compared s).tapes w cap := by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot compareSlots (by decide) _ _ 0
      | exact install_slot compareSlots (by decide) _ _ 1
      | exact install_slot compareSlots (by decide) _ _ 2
      | exact install_slot compareSlots (by decide) _ _ 3
      | exact install_other compareSlots _ _ _ (by decide)
  rw [he] at hr
  exact hr

theorem subtract_layout (s : Store) (w cap : ℕ) (ha : s.head<2^w) (hp : 1 ≤ s.head)
    (hb : s.difference.length≤2*w+1) (hc : 2*w+1≤cap) :
    ReadyRun subtractProgram (4*w+4) (s.tapes w cap) ((subtracted s w).tapes w cap) := by
  have h := subtract_ready w s.head 1 s.difference cap hp ha hb
  simp only [max_eq_left hc] at h
  have hr := h.focus subtractSlots (by decide) (s.tapes w cap)
    (by intro j; fin_cases j <;> rfl)
  have he : install subtractSlots (s.tapes w cap)
      (![frame (binary w s.head),frame (binary w 1),frame (binary w (s.head-1)),
        List.replicate cap false] : Fin 4 → List Bool) = (subtracted s w).tapes w cap := by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot subtractSlots (by decide) _ _ 0
      | exact install_slot subtractSlots (by decide) _ _ 1
      | exact install_slot subtractSlots (by decide) _ _ 2
      | exact install_slot subtractSlots (by decide) _ _ 3
      | exact install_other subtractSlots _ _ _ (by decide)
  rw [he] at hr
  exact hr

theorem copy_layout (s : Store) (w cap : ℕ) (hc : 4*w+3≤cap) :
    ReadyRun copyProgram (8*w+8) ((subtracted s w).tapes w cap)
      ((copied (subtracted s w)).tapes w cap) := by
  have hc' : 2*w+1≤cap := by omega
  have h := copy_ready (binary w (s.head-1)) (frame (binary w s.head)) cap cap (by simp)
  simp only [binary_length,max_eq_left hc,max_eq_left hc'] at h
  have hr := h.focus copySlots (by decide) ((subtracted s w).tapes w cap)
    (by intro j; fin_cases j <;> rfl)
  have he : install copySlots ((subtracted s w).tapes w cap)
      (![frame (binary w (s.head-1)),frame (binary w (s.head-1)),
        List.replicate cap false,List.replicate cap false] : Fin 4 → List Bool) =
        (copied (subtracted s w)).tapes w cap := by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot copySlots (by decide) _ _ 0
      | exact install_slot copySlots (by decide) _ _ 1
      | exact install_slot copySlots (by decide) _ _ 2
      | exact install_slot copySlots (by decide) _ _ 3
      | exact install_other copySlots _ _ _ (by decide)
  rw [he] at hr
  exact hr

theorem increment_layout (s : Store) (w cap : ℕ) (ha : s.head+1<2^w) (hc : 2*w≤cap) :
    ∃ n≤4*w+2, ReadyRun incrementProgram n (s.tapes w cap) ((incremented s).tapes w cap) := by
  obtain ⟨base,hb,ht0,ht1,hh,hs,_⟩ := FramedIncrement.increment_run w s.head cap ha hc
  have hin : (Fin.addCases (motive := fun _ : Fin (1+1) => List Bool)
      (fun _ : Fin 1 => frame (binary w s.head)) (fun _ : Fin 1 => List.replicate cap false)) =
      (![frame (binary w s.head),List.replicate cap false] : Fin 2 → List Bool) := by
    funext i; fin_cases i <;> rfl
  rw [hin] at hb
  obtain ⟨hp,hhalt⟩ := prefix_of_run FramedIncrement.machine (4*w+2) _ base hb
  obtain ⟨r,hr,hf,ht,_⟩ := (hp.enlarge (Nat.le_max_left base.peakTapeCells base.final.tapeCells)).run hhalt
    (Nat.le_max_right base.peakTapeCells base.final.tapeCells)
  have ready : ReadyRun FramedIncrement.machine base.steps
      (![frame (binary w s.head),List.replicate cap false] : Fin 2 → List Bool)
      (![frame (binary w (s.head+1)),List.replicate cap false] : Fin 2 → List Bool) := by
    refine ⟨r,hr,?_,?_,ht⟩
    · funext i
      fin_cases i
      · simpa [hf] using ht0
      · simpa [hf] using ht1
    · intro i; simpa [hf] using hh i
  have h := ready.focus incrementSlots (by decide) (s.tapes w cap)
    (by intro j; fin_cases j <;> rfl)
  have he : install incrementSlots (s.tapes w cap)
      (![frame (binary w (s.head+1)),List.replicate cap false] : Fin 2 → List Bool) =
      (incremented s).tapes w cap := by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot incrementSlots (by decide) _ _ 0
      | exact install_slot incrementSlots (by decide) _ _ 1
      | exact install_other incrementSlots _ _ _ (by decide)
  rw [he] at h
  exact ⟨base.steps,hs,h⟩

end NearCubicWires.RepairOrdinary.HeadUpdate
