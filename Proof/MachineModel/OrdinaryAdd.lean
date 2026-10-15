import Proof.MachineModel.OrdinaryBucketCapacity

/-! Bounded binary addition for the bucket-boundary generator. The machine
scans framed scalar words and overwrites a reusable fixed-width output tape. -/
namespace NearCubicWires.RepairOrdinary.Add
open LocalBitMultitape RadixSemantics
open StablePartition.Workspace (overlay overlay_write overlay_length)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bit (a b carry : Bool) : Bool := xor (xor a b) carry
def carry (a b old : Bool) : Bool := (a && b) || (a && old) || (b && old)
def sum : List Bool → List Bool → Bool → List Bool
  | [], _, _ => []
  | a :: as, b :: bs, old => bit a b old :: sum as bs (carry a b old)
  | _ :: _, [], _ => []
def overflow : List Bool → List Bool → Bool → Bool
  | [], _, old => old
  | a :: as, b :: bs, old => overflow as bs (carry a b old)
  | _ :: _, [], old => old

theorem bit_value (a b old : Bool) :
    (bit a b old).toNat + 2 * (carry a b old).toNat = a.toNat + b.toNat + old.toNat := by
  cases a <;> cases b <;> cases old <;> rfl

@[simp] theorem sum_length (left right : List Bool) (old : Bool) (hw : left.length = right.length) :
    (sum left right old).length = left.length := by
  induction left generalizing right old with
  | nil => rfl
  | cons a left ih =>
    cases right with
    | nil => simp at hw
    | cons b right => simp [sum, ih right (carry a b old) (by simpa using hw)]

theorem sum_value (left right : List Bool) (old : Bool) (hw : left.length = right.length) :
    value (sum left right old) + 2 ^ left.length * (overflow left right old).toNat =
      value left + value right + old.toNat := by
  induction left generalizing right old with
  | nil =>
    have hr : right = [] := List.length_eq_zero_iff.mp (by simpa using hw.symm)
    subst right
    simp [sum, overflow, value]
  | cons a left ih =>
    cases right with
    | nil => simp at hw
    | cons b right =>
      have hi := ih right (carry a b old) (by simpa using hw)
      have hb := bit_value a b old
      simp only [sum, overflow, value, List.length_cons, pow_succ]
      nlinarith

theorem sum_binary (width a b : ℕ) (hfit : a + b < 2 ^ width) :
    sum (SignedSortKey.binary width a) (SignedSortKey.binary width b) false = SignedSortKey.binary width (a + b) := by
  have ha : a < 2 ^ width := by omega
  have hb : b < 2 ^ width := by omega
  have hv := sum_value (SignedSortKey.binary width a) (SignedSortKey.binary width b) false (by simp)
  simp only [SignedSortKey.binary_value _ _ ha, SignedSortKey.binary_value _ _ hb,
    SignedSortKey.binary_length, Bool.toNat_false, Nat.add_zero] at hv
  have hvalue : value (sum (SignedSortKey.binary width a) (SignedSortKey.binary width b) false) = a + b := by
    cases ho : overflow (SignedSortKey.binary width a) (SignedSortKey.binary width b) false <;>
      simp only [ho, Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hv <;> omega
  have he := BoundedCounter.binary_of_value (sum (SignedSortKey.binary width a) (SignedSortKey.binary width b) false)
  rw [sum_length _ _ _ (by simp), SignedSortKey.binary_length, hvalue] at he
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
      some (action (scanState (carry (scanned 0) (scanned 1) (state.val == 3))) .right
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
      some (config (scanState (carry a b old)) left right (leftHead + 1) (rightHead + 1)
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

theorem add_prefix (preLeft preRight left right tailLeft tailRight output backing : List Bool)
    (old : Bool) (hw : left.length = right.length) :
    Prefix machine
      ((preLeft ++ frame left ++ tailLeft).length + (preRight ++ frame right ++ tailRight).length +
        output.length + 2 * left.length + 1 + backing.length)
      (2 * left.length + 1)
      (config (scanState old) (preLeft ++ frame left ++ tailLeft) (preRight ++ frame right ++ tailRight)
        preLeft.length preRight.length output backing)
      (config 4 (preLeft ++ frame left ++ tailLeft) (preRight ++ frame right ++ tailRight)
        (preLeft.length + 2 * left.length) (preRight.length + 2 * right.length)
        (output ++ frame (sum left right old)) backing) := by
  induction left generalizing preLeft preRight right old output with
  | nil =>
    have hr : right = [] := List.length_eq_zero_iff.mp (by simpa using hw.symm)
    subst right
    have hread := Streaming.read_append preLeft tailLeft false
    have hp := finish_step (preLeft ++ frame [] ++ tailLeft) (preRight ++ frame [] ++ tailRight)
      preLeft.length preRight.length output backing old (by simpa [frame, List.append_assoc] using hread)
    refine Prefix.step (by simp; omega) (by cases old <;> rfl) hp ?_
    simpa [sum, frame] using Prefix.refl
      (config 4 (preLeft ++ frame [] ++ tailLeft) (preRight ++ frame [] ++ tailRight)
        preLeft.length preRight.length (output ++ [false]) backing) (by simp; omega)
  | cons a left ih =>
    cases right with
    | nil => simp at hw
    | cons b right =>
      have hlen : left.length = right.length := by simpa using hw
      let lhs := preLeft ++ frame (a :: left) ++ tailLeft
      let rhs := preRight ++ frame (b :: right) ++ tailRight
      let space := lhs.length + rhs.length + output.length + 2 * (a :: left).length + 1 + backing.length
      have ht : Prefix machine space (2 * left.length + 1)
          (config (scanState (carry a b old)) lhs rhs (preLeft.length + 2) (preRight.length + 2)
            (output ++ [true, bit a b old]) backing)
          (config 4 lhs rhs (preLeft.length + 2 * (a :: left).length) (preRight.length + 2 * (b :: right).length)
            (output ++ frame (sum (a :: left) (b :: right) old)) backing) := by
        have hi := ih (preLeft ++ [true, a]) (preRight ++ [true, b]) right
          (output ++ [true, bit a b old]) (carry a b old) hlen
        convert hi using 1 <;> simp [lhs, rhs, space, frame, sum, List.append_assoc, Nat.mul_add,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      have hread : readTapeBit lhs preLeft.length = true := by
        simpa [lhs, frame, List.append_assoc] using Streaming.read_append preLeft (a :: frame left ++ tailLeft) true
      have hl : readTapeBit lhs (preLeft.length + 1) = a := by
        simpa [lhs, frame, List.append_assoc] using Streaming.read_append (preLeft ++ [true]) (frame left ++ tailLeft) a
      have hr : readTapeBit rhs (preRight.length + 1) = b := by
        simpa [rhs, frame, List.append_assoc] using Streaming.read_append (preRight ++ [true]) (frame right ++ tailRight) b
      have hbit := bit_step lhs rhs (preLeft.length + 1) (preRight.length + 1) (output ++ [true]) backing old a b hl hr
      have hp := Prefix.step (by simp [space]; omega :
          (config (bitState old) lhs rhs (preLeft.length + 1) (preRight.length + 1) (output ++ [true]) backing).tapeCells ≤ space)
        (by cases old <;> rfl) hbit (by simpa [List.append_assoc, Nat.add_assoc] using ht)
      have hstart := Prefix.step (by simp [space]; omega :
          (config (scanState old) lhs rhs preLeft.length preRight.length output backing).tapeCells ≤ space)
        (by cases old <;> rfl) (marker_step lhs rhs preLeft.length preRight.length output backing old hread) hp
      convert hstart using 1 <;> simp [lhs, rhs, Nat.mul_add, Nat.add_assoc]

theorem add_run (width a b : ℕ) (backing : List Bool) (hfit : a + b < 2 ^ width)
    (hb : backing.length ≤ 2 * width + 1) :
    ∃ r : ExecutionReceipt 3 5,
      runFrom machine (2 * width + 1)
        (config (scanState false) (frame (SignedSortKey.binary width a)) (frame (SignedSortKey.binary width b)) 0 0 [] backing) = some r ∧
      r.final.tapes 0 = frame (SignedSortKey.binary width a) ∧
      r.final.tapes 1 = frame (SignedSortKey.binary width b) ∧
      r.final.tapes 2 = frame (SignedSortKey.binary width (a + b)) ∧
      r.final.heads 0 = 2 * width ∧ r.final.heads 1 = 2 * width ∧ r.final.heads 2 = 2 * width + 1 ∧
      r.steps = 2 * width + 1 ∧ r.peakTapeCells ≤ 8 * width + 4 := by
  have hp := add_prefix [] [] (SignedSortKey.binary width a) (SignedSortKey.binary width b) [] [] [] backing false (by simp)
  obtain ⟨r, hr, hf, hs, hpeak⟩ := hp.run (by rfl) (by simp; omega)
  have he : (sum (SignedSortKey.binary width a) (SignedSortKey.binary width b) false) =
      SignedSortKey.binary width (a + b) := sum_binary width a b hfit
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

end NearCubicWires.RepairOrdinary.Add
