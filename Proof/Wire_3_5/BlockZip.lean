import Proof.Wire_3_5.BlockOfRun
import Proof.Wire_3_5.BlockCost
import Proof.MachineModel.OrdinaryCompare

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform

/-! ## The fold: a 1-bit state over two framed words, the final state appended to the output -/

namespace ZipFold

/-- The reference fold: low bit first. -/
def fold (f : Bool → Bool → Bool → Bool) : List Bool → List Bool → Bool → Bool
  | [], _, old => old
  | a :: as, b :: bs, old => fold f as bs (f a b old)
  | _ :: _, [], old => old

def scanState (old : Bool) : Fin 5 := if old then 1 else 0
def bitState (old : Bool) : Fin 5 := if old then 3 else 2
def action (state : Fin 5) (moveInput : HeadMove) (output : Option Bool) : Action 3 5 :=
  ⟨state, fun i => if i.val = 2 then output else none,
    fun i => if i.val = 2 then if output.isSome then .right else .stay else moveInput⟩

/-- The fold machine: tape 0 and tape 1 are the framed words, tape 2 the output. -/
def machine (f : Bool → Bool → Bool → Bool) (init : Bool) : Machine 3 5 where
  descriptionBits := 0
  start := scanState init
  halted := fun state => state.val == 4
  rule := fun state scanned => if state.val < 2 then
      if scanned 0 then some (action (bitState (state.val == 1)) .right none)
      else some (action 4 .stay (some (state.val == 1)))
    else if state.val < 4 then some (action (scanState (f (scanned 0) (scanned 1) (state.val == 3))) .right none)
    else none

def config (state : Fin 5) (left right : List Bool) (leftHead rightHead : ℕ) (output : List Bool) :
    Configuration 3 5 := ⟨state, ![leftHead, rightHead, output.length], ![left, right, output]⟩

@[simp] theorem config_cells (state : Fin 5) (left right : List Bool) (leftHead rightHead : ℕ) (output : List Bool) :
    (config state left right leftHead rightHead output).tapeCells = left.length + right.length + output.length := by
  simp [config, Configuration.tapeCells, Fin.sum_univ_succ]
  omega

variable (f : Bool → Bool → Bool → Bool) (init : Bool)

theorem marker_step (left right : List Bool) (leftHead rightHead : ℕ) (output : List Bool) (old : Bool)
    (hr : readTapeBit left leftHead = true) :
    step (machine f init) (config (scanState old) left right leftHead rightHead output) =
      some (config (bitState old) left right (leftHead + 1) (rightHead + 1) output) := by
  cases old <;> simp [step, machine, scanState, bitState, config, Configuration.scanned, hr] <;>
    apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply])

theorem bit_step (left right : List Bool) (leftHead rightHead : ℕ) (output : List Bool) (old a b : Bool)
    (hl : readTapeBit left leftHead = a) (hr : readTapeBit right rightHead = b) :
    step (machine f init) (config (bitState old) left right leftHead rightHead output) =
      some (config (scanState (f a b old)) left right (leftHead + 1) (rightHead + 1) output) := by
  cases old <;> simp [step, machine, scanState, bitState, config, Configuration.scanned, hl, hr] <;>
    apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply])

theorem finish_step (left right : List Bool) (leftHead rightHead : ℕ) (output : List Bool) (old : Bool)
    (hr : readTapeBit left leftHead = false) :
    step (machine f init) (config (scanState old) left right leftHead rightHead output) =
      some (config 4 left right leftHead rightHead (output ++ [old])) := by
  cases old <;> simp [step, machine, scanState, config, Configuration.scanned, hr] <;>
    apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply, Streaming.write_append])

theorem scan_prefix (preLeft preRight left right tailLeft tailRight output : List Bool)
    (old : Bool) (hw : left.length = right.length) :
    Prefix (machine f init)
      ((preLeft ++ frame left ++ tailLeft).length + (preRight ++ frame right ++ tailRight).length + output.length + 1)
      (2 * left.length + 1)
      (config (scanState old) (preLeft ++ frame left ++ tailLeft) (preRight ++ frame right ++ tailRight)
        preLeft.length preRight.length output)
      (config 4 (preLeft ++ frame left ++ tailLeft) (preRight ++ frame right ++ tailRight)
        (preLeft.length + 2 * left.length) (preRight.length + 2 * right.length)
        (output ++ [fold f left right old])) := by
  induction left generalizing preLeft preRight right old with
  | nil =>
    have hr : right = [] := List.length_eq_zero_iff.mp (by simpa using hw.symm)
    subst right
    have hread := Streaming.read_append preLeft tailLeft false
    have hp := finish_step f init (preLeft ++ frame [] ++ tailLeft) (preRight ++ frame [] ++ tailRight)
      preLeft.length preRight.length output old (by simpa [frame, List.append_assoc] using hread)
    refine Prefix.step (by simp) (by cases old <;> rfl) hp ?_
    simpa [fold] using Prefix.refl (p := machine f init)
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
      have ht : Prefix (machine f init) space (2 * left.length + 1)
          (config (scanState (f a b old)) lhs rhs (preLeft.length + 2) (preRight.length + 2) output)
          (config 4 lhs rhs (preLeft.length + 2 * (a :: left).length) (preRight.length + 2 * (b :: right).length)
            (output ++ [fold f (a :: left) (b :: right) old])) := by
        have hi := ih (preLeft ++ [true, a]) (preRight ++ [true, b]) right (f a b old) hlen
        convert hi using 1 <;> simp [lhs, rhs, space, frame, fold, List.append_assoc, Nat.mul_add,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      have hread : readTapeBit lhs preLeft.length = true := by
        simpa [lhs, frame, List.append_assoc] using Streaming.read_append preLeft (a :: frame left ++ tailLeft) true
      have hl : readTapeBit lhs (preLeft.length + 1) = a := by
        simpa [lhs, frame, List.append_assoc] using Streaming.read_append (preLeft ++ [true]) (frame left ++ tailLeft) a
      have hr : readTapeBit rhs (preRight.length + 1) = b := by
        simpa [rhs, frame, List.append_assoc] using Streaming.read_append (preRight ++ [true]) (frame right ++ tailRight) b
      have hbit := bit_step f init lhs rhs (preLeft.length + 1) (preRight.length + 1) output old a b hl hr
      have hp := Prefix.step (by simp [space] : (config (bitState old) lhs rhs (preLeft.length + 1) (preRight.length + 1) output).tapeCells ≤ space)
        (by cases old <;> rfl) hbit (by simpa [Nat.add_assoc] using ht)
      have hstart := Prefix.step (by simp [space] : (config (scanState old) lhs rhs preLeft.length preRight.length output).tapeCells ≤ space)
        (by cases old <;> rfl) (marker_step f init lhs rhs preLeft.length preRight.length output old hread) hp
      convert hstart using 1 <;> simp [lhs, rhs, Nat.mul_add, Nat.add_assoc]

theorem scan_run (preLeft preRight left right tailLeft tailRight output : List Bool)
    (hw : left.length = right.length) :
    ∃ r : ExecutionReceipt 3 5,
      runFrom (machine f init) (2 * left.length + 1)
        (config (scanState init) (preLeft ++ frame left ++ tailLeft) (preRight ++ frame right ++ tailRight)
          preLeft.length preRight.length output) = some r ∧
      r.final = config 4 (preLeft ++ frame left ++ tailLeft) (preRight ++ frame right ++ tailRight)
        (preLeft.length + 2 * left.length) (preRight.length + 2 * right.length)
        (output ++ [fold f left right init]) := by
  have hp := scan_prefix f init preLeft preRight left right tailLeft tailRight output init hw
  obtain ⟨r, hr, hf, _, _⟩ := hp.run (by rfl) (by simp; omega)
  exact ⟨r, hr, hf⟩

end ZipFold

/-- The fold over two framed words at given cursors, as a block: the final state is appended to the
output tape, in `2|left|+1` steps. -/
theorem fold_runs (f : Bool → Bool → Bool → Bool) (init : Bool)
    (preLeft preRight left right tailLeft tailRight output : List Bool) (hw : left.length = right.length) :
    ∃ r, runFrom (ZipFold.machine f init) (2 * left.length + 1)
      ⟨(ZipFold.machine f init).start, ![preLeft.length, preRight.length, output.length],
        ![preLeft ++ frame left ++ tailLeft, preRight ++ frame right ++ tailRight, output]⟩ = some r := by
  obtain ⟨r, hr, _⟩ := ZipFold.scan_run f init preLeft preRight left right tailLeft tailRight output hw
  exact ⟨r, hr⟩

noncomputable def foldBlock (f : Bool → Bool → Bool → Bool) (init : Bool)
    (preLeft preRight left right tailLeft tailRight output : List Bool) (hw : left.length = right.length) :
    Block 3 :=
  ofRunFrom (ZipFold.machine f init) (2 * left.length + 1) ![preLeft.length, preRight.length, output.length]
    ![preLeft ++ frame left ++ tailLeft, preRight ++ frame right ++ tailRight, output]
    (fold_runs f init preLeft preRight left right tailLeft tailRight output hw)

theorem foldBlock_out (f : Bool → Bool → Bool → Bool) (init : Bool)
    (preLeft preRight left right tailLeft tailRight output : List Bool) (hw : left.length = right.length) :
    (foldBlock f init preLeft preRight left right tailLeft tailRight output hw).exitA =
        ![preLeft ++ frame left ++ tailLeft, preRight ++ frame right ++ tailRight,
          output ++ [ZipFold.fold f left right init]] ∧
      (foldBlock f init preLeft preRight left right tailLeft tailRight output hw).exitH =
        ![preLeft.length + 2 * left.length, preRight.length + 2 * right.length, output.length + 1] ∧
      (foldBlock f init preLeft preRight left right tailLeft tailRight output hw).cost = 2 * left.length + 1 := by
  obtain ⟨r, hr, hf⟩ := ZipFold.scan_run f init preLeft preRight left right tailLeft tailRight output hw
  have eA := ofRunFrom_exitA (ZipFold.machine f init) (2 * left.length + 1)
    ![preLeft.length, preRight.length, output.length]
    ![preLeft ++ frame left ++ tailLeft, preRight ++ frame right ++ tailRight, output]
    (fold_runs f init preLeft preRight left right tailLeft tailRight output hw) r hr
  have eH := ofRunFrom_exitH (ZipFold.machine f init) (2 * left.length + 1)
    ![preLeft.length, preRight.length, output.length]
    ![preLeft ++ frame left ++ tailLeft, preRight ++ frame right ++ tailRight, output]
    (fold_runs f init preLeft preRight left right tailLeft tailRight output hw) r hr
  rw [hf] at eA eH
  refine ⟨?_, ?_, rfl⟩
  · rw [foldBlock, eA]; rfl
  · rw [foldBlock, eH]
    funext i
    fin_cases i <;> simp [ZipFold.config]

/-! ## The map: a 1-bit state over two framed words, a framed output word -/

namespace ZipMap

/-- The reference map: the output bit of each position, low bit first. -/
def map (out nxt : Bool → Bool → Bool → Bool) : List Bool → List Bool → Bool → List Bool
  | [], _, _ => []
  | a :: as, b :: bs, old => out a b old :: map out nxt as bs (nxt a b old)
  | _ :: _, [], _ => []

@[simp] theorem map_length (out nxt : Bool → Bool → Bool → Bool) (left right : List Bool) (old : Bool)
    (hw : left.length = right.length) : (map out nxt left right old).length = left.length := by
  induction left generalizing right old with
  | nil => rfl
  | cons a left ih =>
    cases right with
    | nil => simp at hw
    | cons b right => simp [map, ih right _ (by simpa using hw)]

def scanState (old : Bool) : Fin 5 := if old then 1 else 0
def bitState (old : Bool) : Fin 5 := if old then 3 else 2
def action (state : Fin 5) (inputMove : HeadMove) (output : Bool) : Action 3 5 :=
  ⟨state, fun i => if i.val = 2 then some output else none,
    fun i => if i.val = 2 then .right else inputMove⟩

/-- The map machine: tape 0 and tape 1 are the framed words, tape 2 receives the framed output. -/
def machine (out nxt : Bool → Bool → Bool → Bool) (init : Bool) : Machine 3 5 where
  descriptionBits := 0
  start := scanState init
  halted := fun state => state.val == 4
  rule := fun state scanned => if state.val < 2 then
      if scanned 0 then some (action (bitState (state.val == 1)) .right true)
      else some (action 4 .stay false)
    else if state.val < 4 then
      some (action (scanState (nxt (scanned 0) (scanned 1) (state.val == 3))) .right
        (out (scanned 0) (scanned 1) (state.val == 3)))
    else none

def config (state : Fin 5) (left right : List Bool) (leftHead rightHead : ℕ) (output : List Bool) :
    Configuration 3 5 := ⟨state, ![leftHead, rightHead, output.length], ![left, right, output]⟩

@[simp] theorem config_cells (state : Fin 5) (left right : List Bool) (leftHead rightHead : ℕ) (output : List Bool) :
    (config state left right leftHead rightHead output).tapeCells = left.length + right.length + output.length := by
  simp [config, Configuration.tapeCells, Fin.sum_univ_succ]
  omega

variable (out nxt : Bool → Bool → Bool → Bool) (init : Bool)

theorem marker_step (left right : List Bool) (leftHead rightHead : ℕ) (output : List Bool) (old : Bool)
    (hr : readTapeBit left leftHead = true) :
    step (machine out nxt init) (config (scanState old) left right leftHead rightHead output) =
      some (config (bitState old) left right (leftHead + 1) (rightHead + 1) (output ++ [true])) := by
  cases old <;> simp [step, machine, scanState, bitState, config, Configuration.scanned, hr] <;>
    apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply, Streaming.write_append])

theorem bit_step (left right : List Bool) (leftHead rightHead : ℕ) (output : List Bool) (old a b : Bool)
    (hl : readTapeBit left leftHead = a) (hr : readTapeBit right rightHead = b) :
    step (machine out nxt init) (config (bitState old) left right leftHead rightHead output) =
      some (config (scanState (nxt a b old)) left right (leftHead + 1) (rightHead + 1)
        (output ++ [out a b old])) := by
  cases old <;> simp [step, machine, scanState, bitState, config, Configuration.scanned, hl, hr] <;>
    apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply, Streaming.write_append])

theorem finish_step (left right : List Bool) (leftHead rightHead : ℕ) (output : List Bool) (old : Bool)
    (hr : readTapeBit left leftHead = false) :
    step (machine out nxt init) (config (scanState old) left right leftHead rightHead output) =
      some (config 4 left right leftHead rightHead (output ++ [false])) := by
  cases old <;> simp [step, machine, scanState, config, Configuration.scanned, hr] <;>
    apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply, Streaming.write_append])

theorem scan_prefix (preLeft preRight left right tailLeft tailRight output : List Bool)
    (old : Bool) (hw : left.length = right.length) :
    Prefix (machine out nxt init)
      ((preLeft ++ frame left ++ tailLeft).length + (preRight ++ frame right ++ tailRight).length +
        output.length + 2 * left.length + 1)
      (2 * left.length + 1)
      (config (scanState old) (preLeft ++ frame left ++ tailLeft) (preRight ++ frame right ++ tailRight)
        preLeft.length preRight.length output)
      (config 4 (preLeft ++ frame left ++ tailLeft) (preRight ++ frame right ++ tailRight)
        (preLeft.length + 2 * left.length) (preRight.length + 2 * right.length)
        (output ++ frame (map out nxt left right old))) := by
  induction left generalizing preLeft preRight right old output with
  | nil =>
    have hr : right = [] := List.length_eq_zero_iff.mp (by simpa using hw.symm)
    subst right
    have hread := Streaming.read_append preLeft tailLeft false
    have hp := finish_step out nxt init (preLeft ++ frame [] ++ tailLeft) (preRight ++ frame [] ++ tailRight)
      preLeft.length preRight.length output old (by simpa [frame, List.append_assoc] using hread)
    refine Prefix.step (by simp) (by cases old <;> rfl) hp ?_
    simpa [map, frame] using Prefix.refl (p := machine out nxt init)
      (config 4 (preLeft ++ frame [] ++ tailLeft) (preRight ++ frame [] ++ tailRight)
        preLeft.length preRight.length (output ++ [false])) (by simp; omega)
  | cons a left ih =>
    cases right with
    | nil => simp at hw
    | cons b right =>
      have hlen : left.length = right.length := by simpa using hw
      let lhs := preLeft ++ frame (a :: left) ++ tailLeft
      let rhs := preRight ++ frame (b :: right) ++ tailRight
      let space := lhs.length + rhs.length + output.length + 2 * (a :: left).length + 1
      have ht : Prefix (machine out nxt init) space (2 * left.length + 1)
          (config (scanState (nxt a b old)) lhs rhs (preLeft.length + 2) (preRight.length + 2)
            (output ++ [true, out a b old]))
          (config 4 lhs rhs (preLeft.length + 2 * (a :: left).length) (preRight.length + 2 * (b :: right).length)
            (output ++ frame (map out nxt (a :: left) (b :: right) old))) := by
        have hi := ih (preLeft ++ [true, a]) (preRight ++ [true, b]) right
          (output ++ [true, out a b old]) (nxt a b old) hlen
        convert hi using 1 <;> simp [lhs, rhs, space, frame, map, List.append_assoc, Nat.mul_add,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      have hread : readTapeBit lhs preLeft.length = true := by
        simpa [lhs, frame, List.append_assoc] using Streaming.read_append preLeft (a :: frame left ++ tailLeft) true
      have hl : readTapeBit lhs (preLeft.length + 1) = a := by
        simpa [lhs, frame, List.append_assoc] using Streaming.read_append (preLeft ++ [true]) (frame left ++ tailLeft) a
      have hr : readTapeBit rhs (preRight.length + 1) = b := by
        simpa [rhs, frame, List.append_assoc] using Streaming.read_append (preRight ++ [true]) (frame right ++ tailRight) b
      have hbit := bit_step out nxt init lhs rhs (preLeft.length + 1) (preRight.length + 1) (output ++ [true])
        old a b hl hr
      have hp := Prefix.step (by simp [space]; omega :
          (config (bitState old) lhs rhs (preLeft.length + 1) (preRight.length + 1) (output ++ [true])).tapeCells ≤ space)
        (by cases old <;> rfl) hbit (by simpa [List.append_assoc, Nat.add_assoc] using ht)
      have hstart := Prefix.step (by simp [space]; omega :
          (config (scanState old) lhs rhs preLeft.length preRight.length output).tapeCells ≤ space)
        (by cases old <;> rfl) (marker_step out nxt init lhs rhs preLeft.length preRight.length output old hread) hp
      convert hstart using 1 <;> simp [lhs, rhs, Nat.mul_add, Nat.add_assoc]

theorem scan_run (preLeft preRight left right tailLeft tailRight output : List Bool)
    (hw : left.length = right.length) :
    ∃ r : ExecutionReceipt 3 5,
      runFrom (machine out nxt init) (2 * left.length + 1)
        (config (scanState init) (preLeft ++ frame left ++ tailLeft) (preRight ++ frame right ++ tailRight)
          preLeft.length preRight.length output) = some r ∧
      r.final = config 4 (preLeft ++ frame left ++ tailLeft) (preRight ++ frame right ++ tailRight)
        (preLeft.length + 2 * left.length) (preRight.length + 2 * right.length)
        (output ++ frame (map out nxt left right init)) := by
  have hp := scan_prefix out nxt init preLeft preRight left right tailLeft tailRight output init hw
  obtain ⟨r, hr, hf, _, _⟩ := hp.run (by rfl) (by simp [frame_length, map_length out nxt left right init hw]; omega)
  exact ⟨r, hr, hf⟩

end ZipMap

/-- The map over two framed words at given cursors, as a block: the framed output word is appended to
the output tape, in `2|left|+1` steps. -/
theorem map_runs (out nxt : Bool → Bool → Bool → Bool) (init : Bool)
    (preLeft preRight left right tailLeft tailRight output : List Bool) (hw : left.length = right.length) :
    ∃ r, runFrom (ZipMap.machine out nxt init) (2 * left.length + 1)
      ⟨(ZipMap.machine out nxt init).start, ![preLeft.length, preRight.length, output.length],
        ![preLeft ++ frame left ++ tailLeft, preRight ++ frame right ++ tailRight, output]⟩ = some r := by
  obtain ⟨r, hr, _⟩ := ZipMap.scan_run out nxt init preLeft preRight left right tailLeft tailRight output hw
  exact ⟨r, hr⟩

noncomputable def mapBlock (out nxt : Bool → Bool → Bool → Bool) (init : Bool)
    (preLeft preRight left right tailLeft tailRight output : List Bool) (hw : left.length = right.length) :
    Block 3 :=
  ofRunFrom (ZipMap.machine out nxt init) (2 * left.length + 1) ![preLeft.length, preRight.length, output.length]
    ![preLeft ++ frame left ++ tailLeft, preRight ++ frame right ++ tailRight, output]
    (map_runs out nxt init preLeft preRight left right tailLeft tailRight output hw)

theorem mapBlock_out (out nxt : Bool → Bool → Bool → Bool) (init : Bool)
    (preLeft preRight left right tailLeft tailRight output : List Bool) (hw : left.length = right.length) :
    (mapBlock out nxt init preLeft preRight left right tailLeft tailRight output hw).exitA =
        ![preLeft ++ frame left ++ tailLeft, preRight ++ frame right ++ tailRight,
          output ++ frame (ZipMap.map out nxt left right init)] ∧
      (mapBlock out nxt init preLeft preRight left right tailLeft tailRight output hw).exitH =
        ![preLeft.length + 2 * left.length, preRight.length + 2 * right.length,
          output.length + (2 * left.length + 1)] ∧
      (mapBlock out nxt init preLeft preRight left right tailLeft tailRight output hw).cost = 2 * left.length + 1 := by
  obtain ⟨r, hr, hf⟩ := ZipMap.scan_run out nxt init preLeft preRight left right tailLeft tailRight output hw
  have eA := ofRunFrom_exitA (ZipMap.machine out nxt init) (2 * left.length + 1)
    ![preLeft.length, preRight.length, output.length]
    ![preLeft ++ frame left ++ tailLeft, preRight ++ frame right ++ tailRight, output]
    (map_runs out nxt init preLeft preRight left right tailLeft tailRight output hw) r hr
  have eH := ofRunFrom_exitH (ZipMap.machine out nxt init) (2 * left.length + 1)
    ![preLeft.length, preRight.length, output.length]
    ![preLeft ++ frame left ++ tailLeft, preRight ++ frame right ++ tailRight, output]
    (map_runs out nxt init preLeft preRight left right tailLeft tailRight output hw) r hr
  rw [hf] at eA eH
  refine ⟨?_, ?_, rfl⟩
  · rw [mapBlock, eA]; rfl
  · rw [mapBlock, eH]
    funext i
    fin_cases i <;> simp [ZipMap.config, frame_length, ZipMap.map_length out nxt left right init hw]

/-! ## Instances: XOR, AND, masked parity, equality -/

/-- Bitwise XOR of two words. -/
def xorOut (a b _ : Bool) : Bool := xor a b
/-- Bitwise AND (masking). -/
def andOut (a b _ : Bool) : Bool := a && b
/-- The state is unused by the pointwise maps. -/
def keep (_ _ old : Bool) : Bool := old
/-- The masked parity `⊕ᵢ aᵢ·bᵢ` (the trace `⟨τ, a⟩` and the pullback's center-bit parities). -/
def parityStep (a b old : Bool) : Bool := xor old (a && b)
/-- Word equality. -/
def eqStep (a b old : Bool) : Bool := old && (a == b)

theorem map_xor (left right : List Bool) (hw : left.length = right.length) (old : Bool) :
    ZipMap.map xorOut keep left right old = List.zipWith xor left right := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons a left ih =>
    cases right with
    | nil => simp at hw
    | cons b right => simp [ZipMap.map, xorOut, keep, ih right (by simpa using hw)]

theorem map_and (left right : List Bool) (hw : left.length = right.length) (old : Bool) :
    ZipMap.map andOut keep left right old = List.zipWith (· && ·) left right := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons a left ih =>
    cases right with
    | nil => simp at hw
    | cons b right => simp [ZipMap.map, andOut, keep, ih right (by simpa using hw)]

/-- The masked parity is the XOR of the positionwise ANDs, `⊕ᵢ aᵢ·bᵢ` (from `old`). -/
theorem fold_parity (left right : List Bool) (old : Bool) :
    ZipFold.fold parityStep left right old = (List.zipWith (· && ·) left right).foldl xor old := by
  induction left generalizing right old with
  | nil => cases right <;> rfl
  | cons a left ih =>
    cases right with
    | nil => rfl
    | cons b right => simp only [ZipFold.fold, List.zipWith_cons_cons, List.foldl_cons, parityStep, ih]

theorem fold_eq (left right : List Bool) (hw : left.length = right.length) :
    ZipFold.fold eqStep left right true = decide (left = right) := by
  suffices h : ∀ old, ZipFold.fold eqStep left right old = (old && decide (left = right)) by simpa using h true
  induction left generalizing right with
  | nil =>
    intro old
    have : right = [] := List.length_eq_zero_iff.mp (by simpa using hw.symm)
    subst this
    simp [ZipFold.fold]
  | cons a left ih =>
    cases right with
    | nil => simp at hw
    | cons b right =>
      intro old
      rw [ZipFold.fold, ih right (by simpa using hw)]
      cases a <;> cases b <;> cases old <;> simp [eqStep]

/-! ## Costs -/

theorem zip_within {E : Envelope} {cls : BudgetClass} {q k psi len : ℕ} (hq : 1 ≤ q) (hl : len ≤ q)
    (hd : 1 ≤ classDeg E cls) : Within E cls 3 q k psi (2 * len + 1) :=
  Within.of_poly hq (a := 1) (by rw [pow_one]; omega) hd

/-! ## Executable twins -/

theorem zip_twin :
    ZipMap.map xorOut keep [true, false, true, true] [true, true, false, true] false = [false, true, true, false] ∧
      ZipMap.map andOut keep [true, false, true, true] [true, true, false, true] false = [true, false, false, true] ∧
      ZipFold.fold parityStep [true, false, true, true] [true, true, false, true] false = false ∧
      ZipFold.fold parityStep [true, false, true, true] [true, true, true, true] false = true ∧
      ZipFold.fold eqStep [true, false] [true, false] true = true ∧
      ZipFold.fold eqStep [true, false] [true, true] true = false := by decide

end NearCubicWires.WireExponent3_5.Block
