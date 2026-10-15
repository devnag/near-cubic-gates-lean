import Proof.Foundations.OrdinaryMachine

/-!
A local three-tape copying machine with an executed linear-time rewind.
Tape 2 records one unary marker per copied bit; erasing those markers drives
the return of the input and output heads. No head-position inspection or
free configuration reset is available to its transition function.
-/
namespace NearCubicWires.RepairOrdinary.Streaming
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (next : Fin 5) (inputMove outputMove counterMove : HeadMove)
    (output counter : Option Bool) : Action 3 5 where
  nextControl := next
  write := fun t => if t.val = 0 then none else if t.val = 1 then output else counter
  move := fun t => if t.val = 0 then inputMove else if t.val = 1 then outputMove else counterMove

def machine : Machine 3 5 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val == 4
  rule := fun s scanned =>
    if s.val = 0 then
      if scanned 0 then some (action 1 .right .stay .stay none none)
      else some (action 2 .stay .stay .left none none)
    else if s.val = 1 then
      some (action 0 .right .right .right (some (scanned 0)) (some true))
    else if s.val = 2 then
      if scanned 2 then some (action 3 .left .left .left none (some false))
      else some (action 4 .stay .stay .stay none none)
    else if s.val = 3 then
      some (action 2 .left .stay .stay none none)
    else none

def config (state : Fin 5) (input : List Bool) (ih : ℕ)
    (output : List Bool) (oh : ℕ) (counter : List Bool) (ch : ℕ) : Configuration 3 5 where
  control := state
  heads := fun t => if t.val = 0 then ih else if t.val = 1 then oh else ch
  tapes := fun t => if t.val = 0 then input else if t.val = 1 then output else counter

@[simp] theorem config_cells (s : Fin 5) (input output counter : List Bool) (i o c : ℕ) :
    (config s input i output o counter c).tapeCells =
      input.length + output.length + counter.length := by
  simp [Configuration.tapeCells, config, Fin.sum_univ_succ]
  omega

theorem read_append (pre suffix : List Bool) (b : Bool) :
    readTapeBit (pre ++ b :: suffix) pre.length = b := by
  induction pre with
  | nil => rfl
  | cons a pre ih => simp [readTapeBit, List.getD] at *

theorem write_append (pre : List Bool) (b : Bool) :
    writeTapeBit pre pre.length b = pre ++ [b] := by
  induction pre with
  | nil => rfl
  | cons a pre ih => simp [writeTapeBit, ih]

theorem read_counter (k z : ℕ) :
    readTapeBit (List.replicate (k + 1) true ++ List.replicate z false) k = true := by
  induction k with
  | zero => simp [List.replicate_succ, readTapeBit, List.getD]
  | succ k ih => simpa [List.replicate_succ, readTapeBit, List.getD] using ih

theorem read_zeros (z : ℕ) : readTapeBit (List.replicate z false) 0 = false := by
  cases z <;> rfl

theorem erase_counter (k z : ℕ) :
    writeTapeBit (List.replicate (k + 1) true ++ List.replicate z false) k false =
      List.replicate k true ++ List.replicate (z + 1) false := by
  induction k with
  | zero => simp [List.replicate_succ, writeTapeBit]
  | succ k ih => simpa [List.replicate_succ, writeTapeBit] using congrArg (List.cons true) ih

def rewindConfig (k z : ℕ) (input output : List Bool) : Configuration 3 5 :=
  config 2 input (2 * k) output k
    (List.replicate k true ++ List.replicate z false) (k - 1)

def finished (input output : List Bool) (counterSize : ℕ) : Configuration 3 5 :=
  config 4 input 0 output 0 (List.replicate counterSize false) 0

theorem rewind_end_step (z : ℕ) (input output : List Bool) :
    step machine (rewindConfig 0 z input output) = some (finished input output z) := by
  simp [step, machine, rewindConfig, config, Configuration.scanned, read_zeros]
  apply configuration_ext
  · rfl
  · funext t; fin_cases t <;> simp [applyAction, action, finished, config, HeadMove.apply]
  · funext t; fin_cases t <;> simp [applyAction, action, finished, config]

theorem rewind_erase_step (k z : ℕ) (input output : List Bool) :
    step machine (rewindConfig (k + 1) z input output) =
      some (config 3 input (2 * k + 1) output k
        (List.replicate k true ++ List.replicate (z + 1) false) (k - 1)) := by
  simp [step, machine, rewindConfig, config, Configuration.scanned, read_counter]
  apply configuration_ext
  · rfl
  · funext t
    fin_cases t <;> simp [applyAction, action, HeadMove.apply]
    omega
  · funext t
    fin_cases t <;> simp [applyAction, action, erase_counter]

theorem rewind_second_step (k z : ℕ) (input output : List Bool) :
    step machine (config 3 input (2 * k + 1) output k
      (List.replicate k true ++ List.replicate (z + 1) false) (k - 1)) =
        some (rewindConfig k (z + 1) input output) := by
  simp [step, machine, config]
  apply configuration_ext
  · rfl
  · funext t
    fin_cases t <;> simp [applyAction, action, rewindConfig, config, HeadMove.apply]
  · funext t
    fin_cases t <;> simp [applyAction, action, rewindConfig, config]

theorem rewind_run (k z : ℕ) (input output : List Bool) :
    ∃ receipt : ExecutionReceipt 3 5,
      runFrom machine (2 * k + 1) (rewindConfig k z input output) = some receipt ∧
      receipt.final = finished input output (k + z) ∧
      receipt.steps = 2 * k + 1 ∧
      receipt.peakTapeCells ≤ input.length + output.length + k + z := by
  induction k generalizing z with
  | zero =>
    let suffix : ExecutionReceipt 3 5 :=
      ⟨finished input output z, 0, (finished input output z).tapeCells⟩
    have hlast : runFrom machine 0 (finished input output z) = some suffix := by rfl
    have hrun := runFrom_step machine (rewindConfig 0 z input output)
      (finished input output z) suffix (by rfl) (rewind_end_step z input output) hlast
    refine ⟨_, hrun, ?_, rfl, ?_⟩
    · simp [suffix]
    · simp [suffix, finished, rewindConfig]
  | succ k ih =>
    obtain ⟨suffix, htail, hfinal, hsteps, hpeak⟩ := ih (z + 1)
    have hsecond := runFrom_step machine
      (config 3 input (2 * k + 1) output k
        (List.replicate k true ++ List.replicate (z + 1) false) (k - 1))
      (rewindConfig k (z + 1) input output) suffix
      (by rfl) (rewind_second_step k z input output) htail
    have hfirst := runFrom_step machine (rewindConfig (k + 1) z input output)
      (config 3 input (2 * k + 1) output k
        (List.replicate k true ++ List.replicate (z + 1) false) (k - 1))
      _ (by rfl) (rewind_erase_step k z input output) hsecond
    refine ⟨⟨suffix.final, suffix.steps + 1 + 1,
      max (rewindConfig (k + 1) z input output).tapeCells
        (max (config 3 input (2 * k + 1) output k
          (List.replicate k true ++ List.replicate (z + 1) false) (k - 1)).tapeCells
          suffix.peakTapeCells)⟩, ?_, ?_, ?_, ?_⟩
    · have hfuel : 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 := by omega
      rw [hfuel]
      exact hfirst
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfinal
    · dsimp only
      omega
    · simp only [rewindConfig, config_cells, List.length_append,
        List.length_replicate] at hpeak ⊢
      omega

def marks (bs : List Bool) : List Bool := bs.flatMap (fun b => [true, b])

@[simp] theorem marks_length (bs : List Bool) : (marks bs).length = 2 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [marks] at *; omega

@[simp] theorem marks_append (xs ys : List Bool) :
    marks (xs ++ ys) = marks xs ++ marks ys := by
  simp [marks]

theorem frame_append (xs ys : List Bool) : frame (xs ++ ys) = marks xs ++ frame ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa [frame, marks] using congrArg (fun zs => true :: b :: zs) ih

def copyConfig (pre bs : List Bool) : Configuration 3 5 :=
  config 0 (marks pre ++ frame bs) (2 * pre.length) pre pre.length
    (List.replicate pre.length true) pre.length

theorem mark_step (pre : List Bool) (b : Bool) (bs : List Bool) :
    step machine (copyConfig pre (b :: bs)) =
      some (config 1 (marks pre ++ frame (b :: bs)) (2 * pre.length + 1)
        pre pre.length (List.replicate pre.length true) pre.length) := by
  have hread : readTapeBit (marks pre ++ frame (b :: bs)) (2 * pre.length) = true := by
    simpa only [marks_length, frame] using read_append (marks pre) (b :: frame bs) true
  simp [step, machine, copyConfig, config, Configuration.scanned, hread]
  apply configuration_ext
  · rfl
  · funext t; fin_cases t <;> simp [applyAction, action, HeadMove.apply]
  · funext t; fin_cases t <;> simp [applyAction, action]

theorem bit_step (pre : List Bool) (b : Bool) (bs : List Bool) :
    step machine (config 1 (marks pre ++ frame (b :: bs)) (2 * pre.length + 1)
      pre pre.length (List.replicate pre.length true) pre.length) =
        some (copyConfig (pre ++ [b]) bs) := by
  have hread : readTapeBit (marks pre ++ frame (b :: bs)) (2 * pre.length + 1) = b := by
    have h := read_append (marks pre ++ [true]) (frame bs) b
    simpa [frame, List.append_assoc] using h
  have hcounter : writeTapeBit (List.replicate pre.length true) pre.length true =
      List.replicate (pre.length + 1) true := by
    have h := write_append (List.replicate pre.length true) true
    simpa [List.replicate_add] using h
  simp [step, machine, config, Configuration.scanned, hread]
  apply configuration_ext
  · rfl
  · funext t
    fin_cases t <;> simp [applyAction, action, copyConfig, config, HeadMove.apply]
    omega
  · funext t
    fin_cases t <;>
      simp [applyAction, action, copyConfig, config, marks, frame,
        List.append_assoc, write_append, hcounter]

theorem copy_end_step (pre : List Bool) :
    step machine (copyConfig pre []) =
      some (rewindConfig pre.length 0 (marks pre ++ frame []) pre) := by
  have hread : readTapeBit (marks pre ++ frame []) (2 * pre.length) = false := by
    simpa only [marks_length, frame] using read_append (marks pre) [] false
  simp [step, machine, copyConfig, config, Configuration.scanned, hread]
  apply configuration_ext
  · rfl
  · funext t
    fin_cases t <;> simp [applyAction, action, rewindConfig, config, HeadMove.apply]
  · funext t
    fin_cases t <;> simp [applyAction, action, rewindConfig, config]

theorem copy_run_from (pre bs : List Bool) :
    ∃ receipt : ExecutionReceipt 3 5,
      runFrom machine (4 * bs.length + 2 * pre.length + 2) (copyConfig pre bs) = some receipt ∧
      receipt.final = finished (marks pre ++ frame bs) (pre ++ bs) (pre.length + bs.length) ∧
      receipt.steps = 4 * bs.length + 2 * pre.length + 2 ∧
      receipt.peakTapeCells ≤ 4 * (pre.length + bs.length) + 1 := by
  induction bs generalizing pre with
  | nil =>
    obtain ⟨suffix, htail, hfinal, hsteps, hpeak⟩ :=
      rewind_run pre.length 0 (marks pre ++ frame []) pre
    have hrun := runFrom_step machine (copyConfig pre [])
      (rewindConfig pre.length 0 (marks pre ++ frame []) pre) suffix
      (by rfl) (copy_end_step pre) htail
    refine ⟨⟨suffix.final, suffix.steps + 1,
      max (copyConfig pre []).tapeCells suffix.peakTapeCells⟩, ?_, ?_, ?_, ?_⟩
    · simpa using hrun
    · simpa using hfinal
    · dsimp only
      simp only [List.length_nil]
      omega
    · simp only [copyConfig, config_cells, List.length_append, marks_length,
        frame_length, List.length_nil, List.length_replicate] at hpeak ⊢
      omega
  | cons b bs ih =>
    obtain ⟨suffix, htail, hfinal, hsteps, hpeak⟩ := ih (pre ++ [b])
    have hsecond := runFrom_step machine
      (config 1 (marks pre ++ frame (b :: bs)) (2 * pre.length + 1)
        pre pre.length (List.replicate pre.length true) pre.length)
      (copyConfig (pre ++ [b]) bs) suffix (by rfl) (bit_step pre b bs) htail
    have hfirst := runFrom_step machine (copyConfig pre (b :: bs))
      (config 1 (marks pre ++ frame (b :: bs)) (2 * pre.length + 1)
        pre pre.length (List.replicate pre.length true) pre.length)
      _ (by rfl) (mark_step pre b bs) hsecond
    refine ⟨⟨suffix.final, suffix.steps + 1 + 1,
      max (copyConfig pre (b :: bs)).tapeCells
        (max (config 1 (marks pre ++ frame (b :: bs)) (2 * pre.length + 1)
          pre pre.length (List.replicate pre.length true) pre.length).tapeCells
          suffix.peakTapeCells)⟩, ?_, ?_, ?_, ?_⟩
    · have hfuel : 4 * (b :: bs).length + 2 * pre.length + 2 =
          4 * bs.length + 2 * (pre ++ [b]).length + 2 + 1 + 1 := by simp; omega
      rw [hfuel]
      exact hfirst
    · simpa [marks, frame, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hfinal
    · dsimp only
      simp only [List.length_append, List.length_cons, List.length_nil] at hsteps ⊢
      omega
    · simp only [copyConfig, config_cells, List.length_append, marks_length,
        frame_length, List.length_cons, List.length_nil, List.length_replicate] at hpeak ⊢
      omega

theorem copy_run (bs : List Bool) :
    ∃ receipt : ExecutionReceipt 3 5,
      run machine (4 * bs.length + 2)
        (fun t => if t.val = 0 then frame bs else []) = some receipt ∧
      receipt.final = finished (frame bs) bs bs.length ∧
      receipt.steps = 4 * bs.length + 2 ∧
      receipt.peakTapeCells ≤ 4 * bs.length + 1 := by
  obtain ⟨receipt, hrun, hfinal, hsteps, hpeak⟩ := copy_run_from [] bs
  refine ⟨receipt, ?_, ?_, ?_, ?_⟩
  · simpa [run, initialConfiguration, machine, copyConfig, config, marks] using hrun
  · simpa [marks] using hfinal
  · simpa using hsteps
  · simpa using hpeak

def copyProgram : Program where
  tapeCount := 3
  stateCount := 5
  twoTapes := by decide
  machine := machine
  outputTape := 1
  outputFresh := by decide

/-- An actual carrier inhabitant, including a paid rewind of every tape head. -/
def rewoundIdentityCopy : RewoundWordFunction (List Bool) id id
    (fun bs => 4 * bs.length + 2) where
  program := copyProgram
  realizes := by
    intro bs
    obtain ⟨receipt, hrun, hfinal, _, _⟩ := copy_run bs
    refine ⟨receipt, hrun, ?_⟩
    simp [hfinal, finished, config, copyProgram]
  headsReset := by
    intro bs receipt hrun tape
    obtain ⟨actual, ha, hf, _, _⟩ := copy_run bs
    have heq : actual = receipt := Option.some.inj (ha.symm.trans hrun)
    subst receipt
    simp [hf, finished, config]

end NearCubicWires.RepairOrdinary.Streaming
