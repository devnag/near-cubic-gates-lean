import Proof.MachineModel.OrdinaryClaimedTraceComplete
import Proof.MachineModel.OrdinaryMemoryCheckerCost

/-! The exact initialization prefix consumed by the chronological checker.
It writes every framed input/witness cell once, beginning in blank memory.
Execution of the event emitter is separate; these identities fix its literal
output and join that output to the already proved computation-log semantics. -/
namespace NearCubicWires.RepairOrdinary.MemoryInitialization
open LocalBitMultitape MemoryLog
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def writes (tape : ℕ) : ℕ → List Bool → List Event
  | _, [] => []
  | start, b::bs => ⟨(tape,start),false,b⟩ :: writes tape (start+1) bs
def install (memory : Memory) (tape start : ℕ) : List Bool → Memory
  | [] => memory
  | b::bs => install (Function.update memory (tape,start) b) tape (start+1) bs

@[simp] theorem writes_length (tape start : ℕ) (bits : List Bool) :
    (writes tape start bits).length = bits.length := by
  induction bits generalizing start with
  | nil => rfl
  | cons b bs ih => simp [writes, ih]

theorem install_other (memory : Memory) (tape start : ℕ) (bits : List Bool)
    (cell : Cell) (h : cell.1 ≠ tape) :
    install memory tape start bits cell = memory cell := by
  induction bits generalizing memory start with
  | nil => rfl
  | cons b bs ih =>
    rw [install, ih]
    apply Function.update_of_ne
    intro he
    exact h (congrArg Prod.fst he)

theorem install_before (memory : Memory) (tape start : ℕ) (bits : List Bool)
    (address : ℕ) (h : address < start) :
    install memory tape start bits (tape,address) = memory (tape,address) := by
  induction bits generalizing memory start with
  | nil => rfl
  | cons b bs ih =>
    rw [install, ih _ _ (by omega)]
    apply Function.update_of_ne
    intro he
    have := congrArg Prod.snd he
    omega

theorem install_at (memory : Memory) (tape start : ℕ) (bits : List Bool) (index : ℕ) :
    install memory tape start bits (tape,start+index) =
      if index < bits.length then readTapeBit bits index else memory (tape,start+index) := by
  induction bits generalizing memory start index with
  | nil => simp [install]
  | cons b bs ih =>
    cases index with
    | zero =>
      simp only [Nat.add_zero, install]
      rw [install_before _ tape (start+1) bs start (by omega)]
      simp [readTapeBit]
    | succ index =>
      rw [install]
      have he : start+(index+1) = (start+1)+index := by omega
      rw [he, ih]
      have hn : (tape,(start+1)+index) ≠ (tape,start) := by
        intro h
        have := congrArg Prod.snd h
        omega
      simp [Function.update_of_ne hn, readTapeBit]

theorem writes_run (memory : Memory) (tape start : ℕ) (bits : List Bool)
    (fresh : ∀ address, start ≤ address → memory (tape,address) = false) :
    MemoryLog.run memory (writes tape start bits) = some (install memory tape start bits) := by
  induction bits generalizing memory start with
  | nil => rfl
  | cons b bs ih =>
    have htail : ∀ address, start+1 ≤ address →
        Function.update memory (tape,start) b (tape,address) = false := by
      intro address haddr
      have hn : (tape,address) ≠ (tape,start) := by
        intro h
        have := congrArg Prod.snd h
        omega
      rw [Function.update_of_ne hn]
      exact fresh address (by omega)
    simpa only [writes, MemoryLog.run, fresh start (by omega), if_true, install] using
      ih (Function.update memory (tape,start) b) (start+1) htail

def events (input witness : List Bool) : List Event :=
  writes 0 0 (frame input) ++ writes 1 0 (frame witness)
def memory (input witness : List Bool) : Memory :=
  fun cell => if cell.1 = 0 then readTapeBit (frame input) cell.2
    else if cell.1 = 1 then readTapeBit (frame witness) cell.2 else false

theorem initial_count (input witness : List Bool) :
    (events input witness).length = 2*input.length+2*witness.length+2 := by
  simp [events]
  omega

theorem initial_run (input witness : List Bool) :
    MemoryLog.run (fun _ => false) (events input witness) = some (memory input witness) := by
  let first := install (fun _ => false) 0 0 (frame input)
  have hx := writes_run (fun _ => false) 0 0 (frame input) (by intros; rfl)
  have hw := writes_run first 1 0 (frame witness) (by
    intro address _
    exact install_other (fun _ => false) 0 0 (frame input) (1,address) (by simp))
  have hfinal : install first 1 0 (frame witness) = memory input witness := by
    funext cell
    rcases cell with ⟨tape,address⟩
    by_cases h0 : tape = 0
    · subst tape
      rw [install_other _ 1 _ _ (0,address) (by simp)]
      have hat := install_at (fun _ => false) 0 0 (frame input) address
      simp only [Nat.zero_add] at hat
      change install (fun _ => false) 0 0 (frame input) (0,address) = _
      rw [hat]
      simp only [memory, if_true]
      split
      · rfl
      · next h =>
        symm
        exact List.getD_eq_default (frame input) false (by omega)
    · by_cases h1 : tape = 1
      · subst tape
        have hat := install_at first 1 0 (frame witness) address
        simp only [Nat.zero_add] at hat
        rw [hat]
        have hf : first (1,address) = false :=
          install_other (fun _ => false) 0 0 (frame input) (1,address) (by simp)
        simp only [memory, if_true, hf]
        split
        · rfl
        · next h =>
          symm
          exact List.getD_eq_default (frame witness) false (by omega)
      · rw [install_other _ 1 _ _ (tape,address) h1]
        have hf := install_other (fun _ => false) 0 0 (frame input) (tape,address) h0
        simpa only [memory, h0, h1, if_false] using hf
  rw [events, MemoryLog.run_append, hx]
  simpa only [Option.bind_some, hfinal] using hw

end NearCubicWires.RepairOrdinary.MemoryInitialization
