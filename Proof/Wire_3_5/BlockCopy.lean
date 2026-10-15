import Proof.Wire_3_5.BlockZip

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

theorem overlay_exact (out backing : List Bool) (h : backing.length ≤ out.length) : overlay out backing = out := by
  simp [overlay, List.drop_eq_nil_of_le h]

theorem overlay_nil (out : List Bool) : overlay out [] = out := by simp [overlay]

/-! ## The copy machine -/

namespace CopyO

def action (state : Fin 3) (sourceMove : HeadMove) (output : Bool) : Action 2 3 :=
  ⟨state, fun i => if i.val = 1 then some output else none,
    fun i => if i.val = 1 then .right else sourceMove⟩

/-- Tape 0 holds the framed source word; tape 1 receives its copy at the cursor. -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 2
  rule := fun state scanned => if state.val = 0 then
      (if scanned 0 then some (action 1 .right true) else some (action 2 .stay false))
    else if state.val = 1 then some (action 0 .right (scanned 0))
    else none

def config (state : Fin 3) (source : List Bool) (sourceHead : ℕ) (output backing : List Bool) :
    Configuration 2 3 := ⟨state, ![sourceHead, output.length], ![source, overlay output backing]⟩

@[simp] theorem config_cells (state : Fin 3) (source : List Bool) (sourceHead : ℕ) (output backing : List Bool) :
    (config state source sourceHead output backing).tapeCells = source.length + max output.length backing.length := by
  simp [config, Configuration.tapeCells, Fin.sum_univ_succ]

theorem marker_step (source : List Bool) (h : ℕ) (output backing : List Bool) (hr : readTapeBit source h = true) :
    step machine (config 0 source h output backing) = some (config 1 source (h + 1) (output ++ [true]) backing) := by
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, overlay_write]

theorem bit_step (source : List Bool) (h : ℕ) (output backing : List Bool) (b : Bool) (hr : readTapeBit source h = b) :
    step machine (config 1 source h output backing) = some (config 0 source (h + 1) (output ++ [b]) backing) := by
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, overlay_write]

theorem finish_step (source : List Bool) (h : ℕ) (output backing : List Bool) (hr : readTapeBit source h = false) :
    step machine (config 0 source h output backing) = some (config 2 source h (output ++ [false]) backing) := by
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, overlay_write]

theorem copy_prefix (pre w tail output backing : List Bool) :
    Prefix machine ((pre ++ frame w ++ tail).length + (output.length + 2 * w.length + 1) + backing.length)
      (2 * w.length + 1)
      (config 0 (pre ++ frame w ++ tail) pre.length output backing)
      (config 2 (pre ++ frame w ++ tail) (pre.length + 2 * w.length) (output ++ frame w) backing) := by
  induction w generalizing pre output with
  | nil =>
    have hread := Streaming.read_append pre tail false
    have hp := finish_step (pre ++ frame [] ++ tail) pre.length output backing
      (by simpa [frame, List.append_assoc] using hread)
    refine Prefix.step (by simp; omega) rfl hp ?_
    simpa [frame] using Prefix.refl (p := machine)
      (config 2 (pre ++ frame [] ++ tail) pre.length (output ++ [false]) backing) (by simp; omega)
  | cons a w ih =>
    let src := pre ++ frame (a :: w) ++ tail
    let space := src.length + (output.length + 2 * (a :: w).length + 1) + backing.length
    have ht : Prefix machine space (2 * w.length + 1)
        (config 0 src (pre.length + 2) (output ++ [true, a]) backing)
        (config 2 src (pre.length + 2 * (a :: w).length) (output ++ frame (a :: w)) backing) := by
      have hi := ih (pre ++ [true, a]) (output ++ [true, a])
      convert hi using 1 <;> simp [src, space, frame, List.append_assoc, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]
    have hread : readTapeBit src pre.length = true := by
      simpa [src, frame, List.append_assoc] using Streaming.read_append pre (a :: frame w ++ tail) true
    have hbit : readTapeBit src (pre.length + 1) = a := by
      simpa [src, frame, List.append_assoc] using Streaming.read_append (pre ++ [true]) (frame w ++ tail) a
    have hp := Prefix.step (by simp [space]; omega :
        (config 1 src (pre.length + 1) (output ++ [true]) backing).tapeCells ≤ space)
      rfl (bit_step src (pre.length + 1) (output ++ [true]) backing a hbit)
      (by simpa [List.append_assoc, Nat.add_assoc] using ht)
    have hstart := Prefix.step (by simp [space]; omega :
        (config 0 src pre.length output backing).tapeCells ≤ space)
      rfl (marker_step src pre.length output backing hread) hp
    convert hstart using 1 <;> (simp [src, frame, List.append_assoc]; try omega)

theorem copy_run (pre w tail output backing : List Bool) :
    ∃ r : ExecutionReceipt 2 3, runFrom machine (2 * w.length + 1) (config 0 (pre ++ frame w ++ tail) pre.length output backing) = some r ∧
      r.final = config 2 (pre ++ frame w ++ tail) (pre.length + 2 * w.length) (output ++ frame w) backing := by
  obtain ⟨r, hr, hf, _, _⟩ := (copy_prefix pre w tail output backing).run rfl (by simp [frame_length]; omega)
  exact ⟨r, hr, hf⟩

end CopyO

theorem copy_runs (pre w tail output backing : List Bool) :
    ∃ r, runFrom CopyO.machine (2 * w.length + 1)
      ⟨CopyO.machine.start, ![pre.length, output.length], ![pre ++ frame w ++ tail, overlay output backing]⟩ = some r := by
  obtain ⟨r, hr, _⟩ := CopyO.copy_run pre w tail output backing
  exact ⟨r, hr⟩

/-- **Copy** `frame w` from the source cursor onto the output cursor, over the output's backing. -/
noncomputable def copyBlock (pre w tail output backing : List Bool) : Block 2 :=
  ofRunFrom CopyO.machine (2 * w.length + 1) ![pre.length, output.length]
    ![pre ++ frame w ++ tail, overlay output backing] (copy_runs pre w tail output backing)

theorem copyBlock_spec (pre w tail output backing : List Bool) :
    (copyBlock pre w tail output backing).entryH = ![pre.length, output.length] ∧
      (copyBlock pre w tail output backing).entryA = ![pre ++ frame w ++ tail, overlay output backing] ∧
      (copyBlock pre w tail output backing).exitA = ![pre ++ frame w ++ tail, overlay (output ++ frame w) backing] ∧
      (copyBlock pre w tail output backing).exitH = ![pre.length + 2 * w.length, output.length + (2 * w.length + 1)] ∧
      (copyBlock pre w tail output backing).cost = 2 * w.length + 1 := by
  obtain ⟨r, hr, hf⟩ := CopyO.copy_run pre w tail output backing
  have eA := ofRunFrom_exitA _ _ _ _ (copy_runs pre w tail output backing) r hr
  have eH := ofRunFrom_exitH _ _ _ _ (copy_runs pre w tail output backing) r hr
  rw [hf] at eA eH
  refine ⟨rfl, rfl, ?_, ?_, rfl⟩
  · rw [copyBlock, eA]; rfl
  · rw [copyBlock, eH]
    funext i
    fin_cases i <;> simp [CopyO.config, frame_length]

/-! ## The map over a backing -/

namespace ZipMap

def configO (state : Fin 5) (left right : List Bool) (leftHead rightHead : ℕ) (output backing : List Bool) :
    Configuration 3 5 := ⟨state, ![leftHead, rightHead, output.length], ![left, right, overlay output backing]⟩

@[simp] theorem configO_cells (state : Fin 5) (left right : List Bool) (leftHead rightHead : ℕ) (output backing : List Bool) :
    (configO state left right leftHead rightHead output backing).tapeCells =
      left.length + right.length + max output.length backing.length := by
  simp [configO, Configuration.tapeCells, Fin.sum_univ_succ]
  omega

variable (out nxt : Bool → Bool → Bool → Bool) (init : Bool)

theorem marker_stepO (left right : List Bool) (leftHead rightHead : ℕ) (output backing : List Bool) (old : Bool)
    (hr : readTapeBit left leftHead = true) :
    step (machine out nxt init) (configO (scanState old) left right leftHead rightHead output backing) =
      some (configO (bitState old) left right (leftHead + 1) (rightHead + 1) (output ++ [true]) backing) := by
  cases old <;> simp [step, machine, scanState, bitState, configO, Configuration.scanned, hr] <;>
    apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply, overlay_write])

theorem bit_stepO (left right : List Bool) (leftHead rightHead : ℕ) (output backing : List Bool) (old a b : Bool)
    (hl : readTapeBit left leftHead = a) (hr : readTapeBit right rightHead = b) :
    step (machine out nxt init) (configO (bitState old) left right leftHead rightHead output backing) =
      some (configO (scanState (nxt a b old)) left right (leftHead + 1) (rightHead + 1)
        (output ++ [out a b old]) backing) := by
  cases old <;> simp [step, machine, scanState, bitState, configO, Configuration.scanned, hl, hr] <;>
    apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply, overlay_write])

theorem finish_stepO (left right : List Bool) (leftHead rightHead : ℕ) (output backing : List Bool) (old : Bool)
    (hr : readTapeBit left leftHead = false) :
    step (machine out nxt init) (configO (scanState old) left right leftHead rightHead output backing) =
      some (configO 4 left right leftHead rightHead (output ++ [false]) backing) := by
  cases old <;> simp [step, machine, scanState, configO, Configuration.scanned, hr] <;>
    apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply, overlay_write])

theorem scan_prefixO (preLeft preRight left right tailLeft tailRight output backing : List Bool)
    (old : Bool) (hw : left.length = right.length) :
    Prefix (machine out nxt init)
      ((preLeft ++ frame left ++ tailLeft).length + (preRight ++ frame right ++ tailRight).length +
        (output.length + 2 * left.length + 1) + backing.length)
      (2 * left.length + 1)
      (configO (scanState old) (preLeft ++ frame left ++ tailLeft) (preRight ++ frame right ++ tailRight)
        preLeft.length preRight.length output backing)
      (configO 4 (preLeft ++ frame left ++ tailLeft) (preRight ++ frame right ++ tailRight)
        (preLeft.length + 2 * left.length) (preRight.length + 2 * right.length)
        (output ++ frame (map out nxt left right old)) backing) := by
  induction left generalizing preLeft preRight right old output with
  | nil =>
    have hr : right = [] := List.length_eq_zero_iff.mp (by simpa using hw.symm)
    subst right
    have hread := Streaming.read_append preLeft tailLeft false
    have hp := finish_stepO out nxt init (preLeft ++ frame [] ++ tailLeft) (preRight ++ frame [] ++ tailRight)
      preLeft.length preRight.length output backing old (by simpa [frame, List.append_assoc] using hread)
    refine Prefix.step (by simp; omega) (by cases old <;> rfl) hp ?_
    simpa [map, frame] using Prefix.refl (p := machine out nxt init)
      (configO 4 (preLeft ++ frame [] ++ tailLeft) (preRight ++ frame [] ++ tailRight)
        preLeft.length preRight.length (output ++ [false]) backing) (by simp; omega)
  | cons a left ih =>
    cases right with
    | nil => simp at hw
    | cons b right =>
      have hlen : left.length = right.length := by simpa using hw
      let lhs := preLeft ++ frame (a :: left) ++ tailLeft
      let rhs := preRight ++ frame (b :: right) ++ tailRight
      let space := lhs.length + rhs.length + (output.length + 2 * (a :: left).length + 1) + backing.length
      have ht : Prefix (machine out nxt init) space (2 * left.length + 1)
          (configO (scanState (nxt a b old)) lhs rhs (preLeft.length + 2) (preRight.length + 2)
            (output ++ [true, out a b old]) backing)
          (configO 4 lhs rhs (preLeft.length + 2 * (a :: left).length) (preRight.length + 2 * (b :: right).length)
            (output ++ frame (map out nxt (a :: left) (b :: right) old)) backing) := by
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
      have hbit := bit_stepO out nxt init lhs rhs (preLeft.length + 1) (preRight.length + 1) (output ++ [true])
        backing old a b hl hr
      have hp := Prefix.step (by simp [space]; omega :
          (configO (bitState old) lhs rhs (preLeft.length + 1) (preRight.length + 1) (output ++ [true]) backing).tapeCells ≤ space)
        (by cases old <;> rfl) hbit (by simpa [List.append_assoc, Nat.add_assoc] using ht)
      have hstart := Prefix.step (by simp [space]; omega :
          (configO (scanState old) lhs rhs preLeft.length preRight.length output backing).tapeCells ≤ space)
        (by cases old <;> rfl) (marker_stepO out nxt init lhs rhs preLeft.length preRight.length output backing old hread) hp
      convert hstart using 1 <;> simp [lhs, rhs, Nat.mul_add, Nat.add_assoc]

theorem scan_runO (preLeft preRight left right tailLeft tailRight output backing : List Bool)
    (hw : left.length = right.length) :
    ∃ r : ExecutionReceipt 3 5,
      runFrom (machine out nxt init) (2 * left.length + 1)
        (configO (scanState init) (preLeft ++ frame left ++ tailLeft) (preRight ++ frame right ++ tailRight)
          preLeft.length preRight.length output backing) = some r ∧
      r.final = configO 4 (preLeft ++ frame left ++ tailLeft) (preRight ++ frame right ++ tailRight)
        (preLeft.length + 2 * left.length) (preRight.length + 2 * right.length)
        (output ++ frame (map out nxt left right init)) backing := by
  have hp := scan_prefixO out nxt init preLeft preRight left right tailLeft tailRight output backing init hw
  obtain ⟨r, hr, hf, _, _⟩ := hp.run (by rfl) (by simp [frame_length, map_length out nxt left right init hw]; omega)
  exact ⟨r, hr, hf⟩

end ZipMap

theorem mapO_runs (out nxt : Bool → Bool → Bool → Bool) (init : Bool)
    (preLeft preRight left right tailLeft tailRight output backing : List Bool) (hw : left.length = right.length) :
    ∃ r, runFrom (ZipMap.machine out nxt init) (2 * left.length + 1)
      ⟨(ZipMap.machine out nxt init).start, ![preLeft.length, preRight.length, output.length],
        ![preLeft ++ frame left ++ tailLeft, preRight ++ frame right ++ tailRight, overlay output backing]⟩ = some r := by
  obtain ⟨r, hr, _⟩ := ZipMap.scan_runO out nxt init preLeft preRight left right tailLeft tailRight output backing hw
  exact ⟨r, hr⟩

/-- **The map over a backing**: the framed map of two words written at the output cursor. -/
noncomputable def mapBlockO (out nxt : Bool → Bool → Bool → Bool) (init : Bool)
    (preLeft preRight left right tailLeft tailRight output backing : List Bool) (hw : left.length = right.length) :
    Block 3 :=
  ofRunFrom (ZipMap.machine out nxt init) (2 * left.length + 1) ![preLeft.length, preRight.length, output.length]
    ![preLeft ++ frame left ++ tailLeft, preRight ++ frame right ++ tailRight, overlay output backing]
    (mapO_runs out nxt init preLeft preRight left right tailLeft tailRight output backing hw)

theorem mapBlockO_spec (out nxt : Bool → Bool → Bool → Bool) (init : Bool)
    (preLeft preRight left right tailLeft tailRight output backing : List Bool) (hw : left.length = right.length) :
    (mapBlockO out nxt init preLeft preRight left right tailLeft tailRight output backing hw).entryH =
        ![preLeft.length, preRight.length, output.length] ∧
      (mapBlockO out nxt init preLeft preRight left right tailLeft tailRight output backing hw).entryA =
        ![preLeft ++ frame left ++ tailLeft, preRight ++ frame right ++ tailRight, overlay output backing] ∧
      (mapBlockO out nxt init preLeft preRight left right tailLeft tailRight output backing hw).exitA =
        ![preLeft ++ frame left ++ tailLeft, preRight ++ frame right ++ tailRight,
          overlay (output ++ frame (ZipMap.map out nxt left right init)) backing] ∧
      (mapBlockO out nxt init preLeft preRight left right tailLeft tailRight output backing hw).exitH =
        ![preLeft.length + 2 * left.length, preRight.length + 2 * right.length,
          output.length + (2 * left.length + 1)] ∧
      (mapBlockO out nxt init preLeft preRight left right tailLeft tailRight output backing hw).cost =
        2 * left.length + 1 := by
  obtain ⟨r, hr, hf⟩ := ZipMap.scan_runO out nxt init preLeft preRight left right tailLeft tailRight output backing hw
  have eA := ofRunFrom_exitA _ _ _ _ (mapO_runs out nxt init preLeft preRight left right tailLeft tailRight output backing hw) r hr
  have eH := ofRunFrom_exitH _ _ _ _ (mapO_runs out nxt init preLeft preRight left right tailLeft tailRight output backing hw) r hr
  rw [hf] at eA eH
  refine ⟨rfl, rfl, ?_, ?_, rfl⟩
  · rw [mapBlockO, eA]; rfl
  · rw [mapBlockO, eH]
    funext i
    fin_cases i <;> simp [ZipMap.configO, frame_length, ZipMap.map_length out nxt left right init hw]

theorem copy_twin : overlay ([true, false] ++ frame [true]) [false, false, false, false, false, false, true] =
    [true, false, true, true, false, false, true] := by decide

end NearCubicWires.WireExponent3_5.Block
