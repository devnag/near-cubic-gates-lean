import Proof.MachineModel.OrdinaryDominanceLabels

/-! Actual bounded-word comparison for bucket boundaries and cell keys.
Inputs are scanned low bit first; the most recent differing bit determines
the order. The output is appended without rewinding either input cursor. -/
namespace NearCubicWires.RepairOrdinary.Compare
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def next (left right old : Bool) : Bool := if left = right then old else !left
def decision : List Bool → List Bool → Bool → Bool
  | [], _, old => old
  | left :: ls, right :: rs, old => decision ls rs (next left right old)
  | _ :: _, [], old => old

theorem decision_value (left right : List Bool) (old : Bool) (hw : left.length = right.length) :
    decision left right old = if value left = value right then old else decide (value left < value right) := by
  induction left generalizing right old with
  | nil => cases right <;> simp_all [decision, value]
  | cons bit left ih =>
    cases right with
    | nil => simp at hw
    | cons other right =>
      have hlen : left.length = right.length := by simpa using hw
      rw [decision, ih _ _ hlen]
      rcases lt_trichotomy (value left) (value right) with hlt | heq | hgt
      · have hne := ne_of_lt hlt
        cases bit <;> cases other <;> simp [value, hne, hlt] <;> split <;> omega
      · cases bit <;> cases other <;> simp [value, heq, next]
      · have hne := ne_of_gt hgt
        have hn := not_lt_of_gt hgt
        cases bit <;> cases other <;> simp [value, hne, hn] <;> split <;> omega

theorem decision_le (left right : List Bool) (hw : left.length = right.length) :
    decision left right true = decide (value left ≤ value right) := by
  rw [decision_value left right true hw]
  split
  · next h => simp [h]
  · next h =>
      by_cases hl : value left < value right
      · simp [hl, show value left ≤ value right by omega]
      · simp [hl, show ¬value left ≤ value right by omega]

def scanState (old : Bool) : Fin 5 := if old then 1 else 0
def bitState (old : Bool) : Fin 5 := if old then 3 else 2
def action (state : Fin 5) (moveInput : HeadMove) (output : Option Bool) : Action 3 5 :=
  ⟨state, fun i => if i.val = 2 then output else none,
    fun i => if i.val = 2 then if output.isSome then .right else .stay else moveInput⟩
def machine : Machine 3 5 where
  descriptionBits := 0
  start := scanState true
  halted := fun state => state.val == 4
  rule := fun state scanned => if state.val < 2 then
      if scanned 0 then some (action (bitState (state.val == 1)) .right none)
      else some (action 4 .stay (some (state.val == 1)))
    else if state.val < 4 then some (action (scanState (next (scanned 0) (scanned 1) (state.val == 3))) .right none)
    else none

def config (state : Fin 5) (left right : List Bool) (leftHead rightHead : ℕ) (output : List Bool) :
    Configuration 3 5 := ⟨state, ![leftHead, rightHead, output.length], ![left, right, output]⟩

@[simp] theorem config_cells (state : Fin 5) (left right : List Bool) (leftHead rightHead : ℕ) (output : List Bool) :
    (config state left right leftHead rightHead output).tapeCells = left.length + right.length + output.length := by
  simp [config, Configuration.tapeCells, Fin.sum_univ_succ]
  omega

theorem marker_step (left right : List Bool) (leftHead rightHead : ℕ) (output : List Bool) (old : Bool)
    (hr : readTapeBit left leftHead = true) :
    step machine (config (scanState old) left right leftHead rightHead output) =
      some (config (bitState old) left right (leftHead + 1) (rightHead + 1) output) := by
  cases old <;> simp [step, machine, scanState, bitState, config, Configuration.scanned, hr] <;>
    apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply])

theorem bit_step (left right : List Bool) (leftHead rightHead : ℕ) (output : List Bool) (old a b : Bool)
    (hl : readTapeBit left leftHead = a) (hr : readTapeBit right rightHead = b) :
    step machine (config (bitState old) left right leftHead rightHead output) =
      some (config (scanState (next a b old)) left right (leftHead + 1) (rightHead + 1) output) := by
  cases old <;> simp [step, machine, scanState, bitState, config, Configuration.scanned, hl, hr] <;>
    apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply])

theorem finish_step (left right : List Bool) (leftHead rightHead : ℕ) (output : List Bool) (old : Bool)
    (hr : readTapeBit left leftHead = false) :
    step machine (config (scanState old) left right leftHead rightHead output) =
      some (config 4 left right leftHead rightHead (output ++ [old])) := by
  cases old <;> simp [step, machine, scanState, config, Configuration.scanned, hr] <;>
    apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply, Streaming.write_append])

theorem scan_prefix (preLeft preRight left right tailLeft tailRight output : List Bool)
    (old : Bool) (hw : left.length = right.length) :
    Prefix machine
      ((preLeft ++ frame left ++ tailLeft).length + (preRight ++ frame right ++ tailRight).length + output.length + 1)
      (2 * left.length + 1)
      (config (scanState old) (preLeft ++ frame left ++ tailLeft) (preRight ++ frame right ++ tailRight)
        preLeft.length preRight.length output)
      (config 4 (preLeft ++ frame left ++ tailLeft) (preRight ++ frame right ++ tailRight)
        (preLeft.length + 2 * left.length) (preRight.length + 2 * right.length)
        (output ++ [decision left right old])) := by
  induction left generalizing preLeft preRight right old with
  | nil =>
    have hr : right = [] := List.length_eq_zero_iff.mp (by simpa using hw.symm)
    subst right
    have hread := Streaming.read_append preLeft tailLeft false
    have hp := finish_step (preLeft ++ frame [] ++ tailLeft) (preRight ++ frame [] ++ tailRight)
      preLeft.length preRight.length output old (by simpa [frame, List.append_assoc] using hread)
    refine Prefix.step (by simp) (by cases old <;> rfl) hp ?_
    simpa [decision] using Prefix.refl
      (config 4 (preLeft ++ frame [] ++ tailLeft) (preRight ++ frame [] ++ tailRight)
        preLeft.length preRight.length (output ++ [old])) (by simp; omega)
  | cons a left ih =>
    cases right with
    | nil => simp at hw
    | cons b right =>
      have hlen : left.length = right.length := by simpa using hw
      let lhs := preLeft ++ frame (a :: left) ++ tailLeft
      let rhs := preRight ++ frame (b :: right) ++ tailRight
      let space := lhs.length + rhs.length + output.length + 1
      have ht : Prefix machine space (2 * left.length + 1)
          (config (scanState (next a b old)) lhs rhs (preLeft.length + 2) (preRight.length + 2) output)
          (config 4 lhs rhs (preLeft.length + 2 * (a :: left).length) (preRight.length + 2 * (b :: right).length)
            (output ++ [decision (a :: left) (b :: right) old])) := by
        have hi := ih (preLeft ++ [true, a]) (preRight ++ [true, b]) right (next a b old) hlen
        convert hi using 1 <;> simp [lhs, rhs, space, frame, decision, List.append_assoc, Nat.mul_add,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      have hread : readTapeBit lhs preLeft.length = true := by
        simpa [lhs, frame, List.append_assoc] using Streaming.read_append preLeft (a :: frame left ++ tailLeft) true
      have hl : readTapeBit lhs (preLeft.length + 1) = a := by
        simpa [lhs, frame, List.append_assoc] using Streaming.read_append (preLeft ++ [true]) (frame left ++ tailLeft) a
      have hr : readTapeBit rhs (preRight.length + 1) = b := by
        simpa [rhs, frame, List.append_assoc] using Streaming.read_append (preRight ++ [true]) (frame right ++ tailRight) b
      have hbit := bit_step lhs rhs (preLeft.length + 1) (preRight.length + 1) output old a b hl hr
      have hp := Prefix.step (by simp [space] : (config (bitState old) lhs rhs (preLeft.length + 1) (preRight.length + 1) output).tapeCells ≤ space)
        (by cases old <;> rfl) hbit (by simpa [Nat.add_assoc] using ht)
      have hstart := Prefix.step (by simp [space] : (config (scanState old) lhs rhs preLeft.length preRight.length output).tapeCells ≤ space)
        (by cases old <;> rfl) (marker_step lhs rhs preLeft.length preRight.length output old hread) hp
      convert hstart using 1 <;> simp [lhs, rhs, Nat.mul_add, Nat.add_assoc]

theorem compare_run (preLeft preRight left right tailLeft tailRight output : List Bool)
    (hw : left.length = right.length) :
    ∃ r : ExecutionReceipt 3 5,
      runFrom machine (2 * left.length + 1)
        (config (scanState true) (preLeft ++ frame left ++ tailLeft) (preRight ++ frame right ++ tailRight)
          preLeft.length preRight.length output) = some r ∧
      r.final = config 4 (preLeft ++ frame left ++ tailLeft) (preRight ++ frame right ++ tailRight)
        (preLeft.length + 2 * left.length) (preRight.length + 2 * right.length)
        (output ++ [decide (value left ≤ value right)]) ∧
      r.steps = 2 * left.length + 1 ∧
      r.peakTapeCells ≤ (preLeft ++ frame left ++ tailLeft).length +
        (preRight ++ frame right ++ tailRight).length + output.length + 1 := by
  have hp := scan_prefix preLeft preRight left right tailLeft tailRight output true hw
  obtain ⟨r, hr, hf, hs, hb⟩ := hp.run (by rfl) (by simp; omega)
  exact ⟨r, hr, by simpa only [decision_le left right hw] using hf, hs, hb⟩

end NearCubicWires.RepairOrdinary.Compare
