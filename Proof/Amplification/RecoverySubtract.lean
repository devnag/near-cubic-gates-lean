import Proof.Amplification.RecoveryNPBridge
import Proof.MachineModel.OrdinaryAdd

/-! Fixed-width binary subtraction for polynomial recovery simulation and compact SAT decoding. The machine
scans framed scalar words and overwrites a reusable fixed-width output tape. -/
namespace NearCubicWires.RepairSource.RecoveryOracle.Subtract
open RepairOrdinary LocalBitMultitape RadixSemantics
open StablePartition.Workspace (overlay overlay_write overlay_length)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bit (a b borrow : Bool) : Bool := xor (xor a b) borrow
def borrow (a b old : Bool) : Bool := (!a && b) || (!a && old) || (b && old)
def difference : List Bool → List Bool → Bool → List Bool
  | [], _, _ => []
  | a :: as, b :: bs, old => bit a b old :: difference as bs (borrow a b old)
  | _ :: _, [], _ => []
def underflow : List Bool → List Bool → Bool → Bool
  | [], _, old => old
  | a :: as, b :: bs, old => underflow as bs (borrow a b old)
  | _ :: _, [], old => old

theorem bit_value (a b old : Bool) :
    (bit a b old).toNat + b.toNat + old.toNat = a.toNat + 2 * (borrow a b old).toNat := by
  cases a <;> cases b <;> cases old <;> rfl

@[simp] theorem difference_length (left right : List Bool) (old : Bool) (hw : left.length = right.length) :
    (difference left right old).length = left.length := by
  induction left generalizing right old with
  | nil => rfl
  | cons a left ih =>
    cases right with
    | nil => simp at hw
    | cons b right => simp [difference, ih right (borrow a b old) (by simpa using hw)]

theorem difference_value (left right : List Bool) (old : Bool) (hw : left.length = right.length) :
    value (difference left right old) + value right + old.toNat =
      value left + 2 ^ left.length * (underflow left right old).toNat := by
  induction left generalizing right old with
  | nil =>
    have hr : right = [] := List.length_eq_zero_iff.mp (by simpa using hw.symm)
    subst right
    simp [difference, underflow, value]
  | cons a left ih =>
    cases right with
    | nil => simp at hw
    | cons b right =>
      have hi := ih right (borrow a b old) (by simpa using hw)
      have hb := bit_value a b old
      simp only [difference, underflow, value, List.length_cons, pow_succ]
      nlinarith

theorem difference_binary (width a b : ℕ) (hfit : a < 2 ^ width) (hle : b ≤ a) :
    difference (SignedSortKey.binary width a) (SignedSortKey.binary width b) false =
      SignedSortKey.binary width (a - b) := by
  have hb : b < 2 ^ width := by omega
  have hv := difference_value (SignedSortKey.binary width a) (SignedSortKey.binary width b) false (by simp)
  simp only [SignedSortKey.binary_value _ _ hfit, SignedSortKey.binary_value _ _ hb,
    SignedSortKey.binary_length, Bool.toNat_false, Nat.add_zero] at hv
  have hbound := value_lt (difference (SignedSortKey.binary width a) (SignedSortKey.binary width b) false)
  rw [difference_length _ _ _ (by simp), SignedSortKey.binary_length] at hbound
  have hvalue : value (difference (SignedSortKey.binary width a) (SignedSortKey.binary width b) false) = a - b := by
    cases ho : underflow (SignedSortKey.binary width a) (SignedSortKey.binary width b) false <;>
      simp only [ho, Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hv <;> omega
  have he := BoundedCounter.binary_of_value (difference (SignedSortKey.binary width a) (SignedSortKey.binary width b) false)
  rw [difference_length _ _ _ (by simp), SignedSortKey.binary_length, hvalue] at he
  exact he.symm

def scanState (old : Bool) : Fin 5 := if old then 1 else 0
def bitState (old : Bool) : Fin 5 := if old then 3 else 2
def action (state : Fin 5) (inputMove : HeadMove) (output : Bool) : Action 3 5 :=
  ⟨state, fun i => if i.val = 2 then some output else none,
    fun i => if i.val = 2 then .right else inputMove⟩
def machine : Machine 3 5 where
  descriptionBits := 0
  start := scanState false
  halted := fun state => state.val == 4
  rule := fun state scanned => if state.val < 2 then
      if scanned 0 then some (action (bitState (state.val == 1)) .right true)
      else some (action 4 .stay false)
    else if state.val < 4 then
      some (action (scanState (borrow (scanned 0) (scanned 1) (state.val == 3))) .right
        (bit (scanned 0) (scanned 1) (state.val == 3)))
    else none

def config (state : Fin 5) (left right : List Bool) (leftHead rightHead : ℕ)
    (output backing : List Bool) : Configuration 3 5 :=
  ⟨state, ![leftHead, rightHead, output.length], ![left, right, overlay output backing]⟩

@[simp] theorem config_cells (state : Fin 5) (left right : List Bool) (leftHead rightHead : ℕ)
    (output backing : List Bool) :
    (config state left right leftHead rightHead output backing).tapeCells =
      left.length + right.length + max output.length backing.length := by
  simp [config, Configuration.tapeCells, Fin.sum_univ_succ]
  omega

theorem marker_step (left right : List Bool) (leftHead rightHead : ℕ) (output backing : List Bool) (old : Bool)
    (hr : readTapeBit left leftHead = true) :
    step machine (config (scanState old) left right leftHead rightHead output backing) =
      some (config (bitState old) left right (leftHead + 1) (rightHead + 1) (output ++ [true]) backing) := by
  cases old <;> simp [step, machine, scanState, bitState, config, Configuration.scanned, hr] <;>
    apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply, overlay_write])

theorem bit_step (left right : List Bool) (leftHead rightHead : ℕ) (output backing : List Bool) (old a b : Bool)
    (hl : readTapeBit left leftHead = a) (hr : readTapeBit right rightHead = b) :
    step machine (config (bitState old) left right leftHead rightHead output backing) =
      some (config (scanState (borrow a b old)) left right (leftHead + 1) (rightHead + 1)
        (output ++ [bit a b old]) backing) := by
  cases old <;> simp [step, machine, scanState, bitState, config, Configuration.scanned, hl, hr] <;>
    apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply, overlay_write])

theorem finish_step (left right : List Bool) (leftHead rightHead : ℕ) (output backing : List Bool) (old : Bool)
    (hr : readTapeBit left leftHead = false) :
    step machine (config (scanState old) left right leftHead rightHead output backing) =
      some (config 4 left right leftHead rightHead (output ++ [false]) backing) := by
  cases old <;> simp [step, machine, scanState, config, Configuration.scanned, hr] <;>
    apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply, overlay_write])

theorem subtract_prefix (preLeft preRight left right tailLeft tailRight output backing : List Bool)
    (old : Bool) (hw : left.length = right.length) :
    Prefix machine
      ((preLeft ++ RepairOrdinary.frame left ++ tailLeft).length + (preRight ++ RepairOrdinary.frame right ++ tailRight).length +
        output.length + 2 * left.length + 1 + backing.length)
      (2 * left.length + 1)
      (config (scanState old) (preLeft ++ RepairOrdinary.frame left ++ tailLeft) (preRight ++ RepairOrdinary.frame right ++ tailRight)
        preLeft.length preRight.length output backing)
      (config 4 (preLeft ++ RepairOrdinary.frame left ++ tailLeft) (preRight ++ RepairOrdinary.frame right ++ tailRight)
        (preLeft.length + 2 * left.length) (preRight.length + 2 * right.length)
        (output ++ RepairOrdinary.frame (difference left right old)) backing) := by
  induction left generalizing preLeft preRight right old output with
  | nil =>
    have hr : right = [] := List.length_eq_zero_iff.mp (by simpa using hw.symm)
    subst right
    have hread := Streaming.read_append preLeft tailLeft false
    have hp := finish_step (preLeft ++ RepairOrdinary.frame [] ++ tailLeft) (preRight ++ RepairOrdinary.frame [] ++ tailRight)
      preLeft.length preRight.length output backing old (by simpa [RepairOrdinary.frame, List.append_assoc] using hread)
    refine Prefix.step (by simp; omega) (by cases old <;> rfl) hp ?_
    simpa [difference, RepairOrdinary.frame] using Prefix.refl
      (config 4 (preLeft ++ RepairOrdinary.frame [] ++ tailLeft) (preRight ++ RepairOrdinary.frame [] ++ tailRight)
        preLeft.length preRight.length (output ++ [false]) backing) (by simp; omega)
  | cons a left ih =>
    cases right with
    | nil => simp at hw
    | cons b right =>
      have hlen : left.length = right.length := by simpa using hw
      let lhs := preLeft ++ RepairOrdinary.frame (a :: left) ++ tailLeft
      let rhs := preRight ++ RepairOrdinary.frame (b :: right) ++ tailRight
      let space := lhs.length + rhs.length + output.length + 2 * (a :: left).length + 1 + backing.length
      have ht : Prefix machine space (2 * left.length + 1)
          (config (scanState (borrow a b old)) lhs rhs (preLeft.length + 2) (preRight.length + 2)
            (output ++ [true, bit a b old]) backing)
          (config 4 lhs rhs (preLeft.length + 2 * (a :: left).length) (preRight.length + 2 * (b :: right).length)
            (output ++ RepairOrdinary.frame (difference (a :: left) (b :: right) old)) backing) := by
        have hi := ih (preLeft ++ [true, a]) (preRight ++ [true, b]) right
          (output ++ [true, bit a b old]) (borrow a b old) hlen
        convert hi using 1 <;> simp [lhs, rhs, space, RepairOrdinary.frame, difference, List.append_assoc, Nat.mul_add,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      have hread : readTapeBit lhs preLeft.length = true := by
        simpa [lhs, RepairOrdinary.frame, List.append_assoc] using Streaming.read_append preLeft (a :: RepairOrdinary.frame left ++ tailLeft) true
      have hl : readTapeBit lhs (preLeft.length + 1) = a := by
        simpa [lhs, RepairOrdinary.frame, List.append_assoc] using Streaming.read_append (preLeft ++ [true]) (RepairOrdinary.frame left ++ tailLeft) a
      have hr : readTapeBit rhs (preRight.length + 1) = b := by
        simpa [rhs, RepairOrdinary.frame, List.append_assoc] using Streaming.read_append (preRight ++ [true]) (RepairOrdinary.frame right ++ tailRight) b
      have hbit := bit_step lhs rhs (preLeft.length + 1) (preRight.length + 1) (output ++ [true]) backing old a b hl hr
      have hp := Prefix.step (by simp [space]; omega :
          (config (bitState old) lhs rhs (preLeft.length + 1) (preRight.length + 1) (output ++ [true]) backing).tapeCells ≤ space)
        (by cases old <;> rfl) hbit (by simpa [List.append_assoc, Nat.add_assoc] using ht)
      have hstart := Prefix.step (by simp [space]; omega :
          (config (scanState old) lhs rhs preLeft.length preRight.length output backing).tapeCells ≤ space)
        (by cases old <;> rfl) (marker_step lhs rhs preLeft.length preRight.length output backing old hread) hp
      convert hstart using 1 <;> simp [lhs, rhs, Nat.mul_add, Nat.add_assoc]

theorem subtract_run (width a b : ℕ) (backing : List Bool) (hfit : a < 2 ^ width) (hle : b ≤ a)
    (hb : backing.length ≤ 2 * width + 1) :
    ∃ r : ExecutionReceipt 3 5,
      runFrom machine (2 * width + 1)
        (config (scanState false) (RepairOrdinary.frame (SignedSortKey.binary width a)) (RepairOrdinary.frame (SignedSortKey.binary width b)) 0 0 [] backing) = some r ∧
      r.final.tapes 0 = RepairOrdinary.frame (SignedSortKey.binary width a) ∧
      r.final.tapes 1 = RepairOrdinary.frame (SignedSortKey.binary width b) ∧
      r.final.tapes 2 = RepairOrdinary.frame (SignedSortKey.binary width (a - b)) ∧
      r.final.heads 0 = 2 * width ∧ r.final.heads 1 = 2 * width ∧ r.final.heads 2 = 2 * width + 1 ∧
      r.steps = 2 * width + 1 ∧ r.peakTapeCells ≤ 8 * width + 4 := by
  have hp := subtract_prefix [] [] (SignedSortKey.binary width a) (SignedSortKey.binary width b) [] [] [] backing false (by simp)
  obtain ⟨r, hr, hf, hs, hpeak⟩ := hp.run (by rfl) (by simp; omega)
  have he : (difference (SignedSortKey.binary width a) (SignedSortKey.binary width b) false) =
      SignedSortKey.binary width (a - b) := difference_binary width a b hfit hle
  rw [he] at hf
  refine ⟨r, by simpa using hr, by simp [hf, config], by simp [hf, config],
    ?_, ?_, ?_, ?_, by simpa using hs, ?_⟩
  · simp [hf, config, overlay, List.drop_eq_nil_iff.mpr (by simpa using hb)]
  · simp [hf, config]
  · simp [hf, config]
  · simp [hf, config]
  · simp only [List.nil_append, List.append_nil, List.length_nil, Nat.add_zero, frame_length,
      SignedSortKey.binary_length] at hpeak
    omega

end NearCubicWires.RepairSource.RecoveryOracle.Subtract
