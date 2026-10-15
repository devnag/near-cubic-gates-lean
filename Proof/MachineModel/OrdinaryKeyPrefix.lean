import Proof.MachineModel.OrdinaryDominanceScan

/-! Append a bounded prefix of a framed local record. A second framed word
controls its width; the source need not end at that boundary. Only the three
bounded local heads are reset. The growing output cursor is preserved. -/
namespace NearCubicWires.RepairOrdinary.KeyPrefix
open LocalBitMultitape Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (state : Fin 4) (localMove outMove counterMove : HeadMove)
    (outWrite counterWrite : Option Bool) : Action 4 4 :=
  ⟨state, ![none, none, outWrite, counterWrite], ![localMove, localMove, outMove, counterMove]⟩
def machine : Machine 4 4 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 3
  rule := fun state scanned => if state.val = 0 then
      if scanned 1 then some (action 1 .right .right .right (some true) (some true))
      else some (action 2 .stay .stay .left none none)
    else if state.val = 1 then some (action 0 .right .right .right (some (scanned 0)) (some true))
    else if state.val = 2 then
      if scanned 3 then some (action 2 .left .stay .left none (some false))
      else some (action 3 .stay .stay .stay none none)
    else none

def scan (state : Fin 4) (source template : List Bool) (pos : ℕ) (out : List Bool) : Configuration 4 4 :=
  ⟨state, ![pos, pos, out.length, pos], ![source, template, out, List.replicate pos true]⟩
def reset (state : Fin 4) (source template out : List Bool) (remaining erased : ℕ) : Configuration 4 4 :=
  ⟨state, ![remaining, remaining, out.length, remaining - 1],
    ![source, template, out, List.replicate remaining true ++ List.replicate erased false]⟩

@[simp] theorem scan_cells (state : Fin 4) (source template : List Bool) (pos : ℕ) (out : List Bool) :
    (scan state source template pos out).tapeCells = source.length + template.length + out.length + pos := by
  simp [scan, Configuration.tapeCells, Fin.sum_univ_succ, Nat.add_assoc]
@[simp] theorem reset_cells (state : Fin 4) (source template out : List Bool) (remaining erased : ℕ) :
    (reset state source template out remaining erased).tapeCells =
      source.length + template.length + out.length + remaining + erased := by
  simp [reset, Configuration.tapeCells, Fin.sum_univ_succ, Nat.add_assoc]

theorem marker_step (source pre tail out : List Bool) :
    step machine (scan 0 source (pre ++ true :: tail) pre.length out) =
      some (scan 1 source (pre ++ true :: tail) (pre.length + 1) (out ++ [true])) := by
  simp [step, machine, scan, Configuration.scanned, read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction, action, write_append, List.replicate_add]
    simpa using write_append (List.replicate pre.length true) true

theorem bit_step (pre tail template out : List Bool) (bit : Bool) :
    step machine (scan 1 (pre ++ bit :: tail) template pre.length out) =
      some (scan 0 (pre ++ bit :: tail) template (pre.length + 1) (out ++ [bit])) := by
  simp [step, machine, scan, Configuration.scanned, read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction, action, write_append, List.replicate_add]
    simpa using write_append (List.replicate pre.length true) true

theorem delimiter_step (source pre tail out : List Bool) :
    step machine (scan 0 source (pre ++ false :: tail) pre.length out) =
      some (reset 2 source (pre ++ false :: tail) out pre.length 0) := by
  simp [step, machine, scan, Configuration.scanned, read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply, reset]
  · funext i; fin_cases i <;> simp [applyAction, action, reset]

theorem rewind_step (source template out : List Bool) (remaining erased : ℕ) :
    step machine (reset 2 source template out (remaining + 1) erased) =
      some (reset 2 source template out remaining (erased + 1)) := by
  simp [step, machine, reset, Configuration.scanned, read_counter]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, erase_counter]

theorem stop_step (source template out : List Bool) (erased : ℕ) :
    step machine (reset 2 source template out 0 erased) = some (reset 3 source template out 0 erased) := by
  simp [step, machine, reset, Configuration.scanned, read_zeros]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem reset_prefix (source template out : List Bool) (remaining erased : ℕ) :
    Prefix machine (source.length + template.length + out.length + remaining + erased) (remaining + 1)
      (reset 2 source template out remaining erased) (reset 3 source template out 0 (remaining + erased)) := by
  induction remaining generalizing erased with
  | zero =>
    simpa using Prefix.step (by simp : (reset 2 source template out 0 erased).tapeCells ≤
      source.length + template.length + out.length + erased) (by rfl : machine.halted (2 : Fin 4) = false)
      (stop_step source template out erased) (Prefix.refl _ (by simp))
  | succ remaining ih =>
    have hp := Prefix.step (by simp; omega : (reset 2 source template out (remaining + 1) erased).tapeCells ≤
      source.length + template.length + out.length + remaining + (erased + 1))
      (by rfl : machine.halted (2 : Fin 4) = false) (rewind_step source template out remaining erased) (ih (erased + 1))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp

theorem scan_prefix (pre bits suffix templatePre templateBits out : List Bool)
    (hpre : pre.length = templatePre.length) (hwidth : bits.length = templateBits.length) :
    let source := pre ++ marks bits ++ suffix
    let template := templatePre ++ frame templateBits
    Prefix machine (source.length + template.length + out.length + pre.length + 4 * bits.length)
      (2 * bits.length + 1) (scan 0 source template pre.length out)
      (reset 2 source template (out ++ marks bits) (pre.length + 2 * bits.length) 0) := by
  induction bits generalizing pre templatePre templateBits out with
  | nil =>
    have ht : templateBits = [] := List.length_eq_zero_iff.mp (by simpa using hwidth.symm)
    subst templateBits
    have hp := Prefix.step (by simp : (scan 0 (pre ++ suffix) (templatePre ++ [false]) pre.length out).tapeCells ≤
        (pre ++ suffix).length + (templatePre ++ [false]).length + out.length + pre.length)
      (by rfl : machine.halted (0 : Fin 4) = false)
      (by simpa only [hpre] using delimiter_step (pre ++ suffix) templatePre [] out)
      (Prefix.refl _ (by simp [hpre]))
    simpa [marks, frame, hpre] using hp
  | cons bit bits ih =>
    cases templateBits with
    | nil => simp at hwidth
    | cons templateBit templateBits =>
      have hw : bits.length = templateBits.length := by simpa using hwidth
      let source := pre ++ marks (bit :: bits) ++ suffix
      let template := templatePre ++ frame (templateBit :: templateBits)
      let space := source.length + template.length + out.length + pre.length + 4 * (bit :: bits).length
      have hs : (pre ++ [true, bit]) ++ marks bits ++ suffix = source := by simp [source, marks, List.append_assoc]
      have ht : (templatePre ++ [true, templateBit]) ++ frame templateBits = template := by
        simp [template, frame, List.append_assoc]
      have htail : Prefix machine space (2 * bits.length + 1)
          (scan 0 source template (pre.length + 2) (out ++ [true, bit]))
          (reset 2 source template (out ++ marks (bit :: bits)) (pre.length + 2 * (bit :: bits).length) 0) := by
        have hi := ih (pre ++ [true, bit]) (templatePre ++ [true, templateBit]) templateBits (out ++ [true, bit])
          (by simpa using hpre) hw
        dsimp only at hi
        rw [hs, ht] at hi
        convert hi using 1 <;> simp [space, marks, List.append_assoc, Nat.mul_add,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        omega
      have hb : step machine (scan 1 source template (pre.length + 1) (out ++ [true])) =
          some (scan 0 source template (pre.length + 2) (out ++ [true, bit])) := by
        simpa [source, marks, List.append_assoc] using
          bit_step (pre ++ [true]) (marks bits ++ suffix) template (out ++ [true]) bit
      have h1 := Prefix.step (by simp [space]; omega :
          (scan 1 source template (pre.length + 1) (out ++ [true])).tapeCells ≤ space)
        (by rfl : machine.halted (1 : Fin 4) = false)
        hb htail
      have h0 := Prefix.step (by simp [space] : (scan 0 source template pre.length out).tapeCells ≤ space)
        (by rfl : machine.halted (0 : Fin 4) = false)
        (by simpa [template, frame, hpre] using marker_step source templatePre (templateBit :: frame templateBits) out) h1
      convert h0 using 1; simp [Nat.mul_add, Nat.add_assoc]

theorem copy_run (bits suffix templateBits out : List Bool) (hwidth : bits.length = templateBits.length) :
    ∃ r : ExecutionReceipt 4 4,
      runFrom machine (4 * bits.length + 2) (scan 0 (marks bits ++ suffix) (frame templateBits) 0 out) = some r ∧
      r.final = reset 3 (marks bits ++ suffix) (frame templateBits) (out ++ marks bits) 0 (2 * bits.length) ∧
      r.steps = 4 * bits.length + 2 ∧
      r.peakTapeCells ≤ (marks bits ++ suffix).length + (frame templateBits).length + out.length + 4 * bits.length := by
  have hs := scan_prefix [] bits suffix [] templateBits out rfl hwidth
  simp only [List.nil_append, List.length_nil, Nat.add_zero, Nat.zero_add] at hs
  have hr := reset_prefix (marks bits ++ suffix) (frame templateBits) (out ++ marks bits) (2 * bits.length) 0
  let space := (marks bits ++ suffix).length + (frame templateBits).length + out.length + 4 * bits.length
  have hj := hs.trans (hr.enlarge (large := space) (by dsimp [space]; simp; omega))
  obtain ⟨r, hrun, hf, hsteps, hp⟩ := hj.run (by rfl) (by simp; omega)
  refine ⟨r, ?_, by simpa using hf, ?_, hp⟩
  · have he : (2 * bits.length + 1) + (2 * bits.length + 1) = 4 * bits.length + 2 := by omega
    rw [he] at hrun
    exact hrun
  · omega

end NearCubicWires.RepairOrdinary.KeyPrefix
