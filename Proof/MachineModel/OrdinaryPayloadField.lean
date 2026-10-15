import Proof.MachineModel.OrdinaryCrossGrid

/-! Actual sequential payload selection: emit or skip the first bit of one
framed key record, discard its key fields, and retain both global cursors. -/
namespace NearCubicWires.RepairOrdinary.PayloadField
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (state : Fin 5) (outMove : HeadMove) (outWrite : Option Bool) : Action 2 5 :=
  ⟨state, ![none, outWrite], ![.right, outMove]⟩
def machine (keep : Bool) : Machine 2 5 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 4
  rule := fun state scanned => if state.val = 0 then
      some (action (if scanned 0 then 1 else 4) .stay none)
    else if state.val = 1 then some (action 2 (if keep then .right else .stay)
      (if keep then some (scanned 0) else none))
    else if state.val = 2 then some (action (if scanned 0 then 3 else 4) .stay none)
    else if state.val = 3 then some (action 2 .stay none)
    else none

def config (state : Fin 5) (source : List Bool) (pos : ℕ) (out : List Bool) : Configuration 2 5 :=
  ⟨state, ![pos, out.length], ![source, out]⟩
@[simp] theorem config_cells (state : Fin 5) (source : List Bool) (pos : ℕ) (out : List Bool) :
    (config state source pos out).tapeCells = source.length + out.length := by
  simp [config, Configuration.tapeCells, Fin.sum_univ_succ]

theorem marker_step (keep : Bool) (pre tail out : List Bool) :
    step (machine keep) (config 0 (pre ++ true :: tail) pre.length out) =
      some (config 1 (pre ++ true :: tail) (pre.length + 1) out) := by
  simp [step, machine, config, Configuration.scanned, Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem payload_step (keep bit : Bool) (pre tail out : List Bool) :
    step (machine keep) (config 1 (pre ++ bit :: tail) pre.length out) =
      some (config 2 (pre ++ bit :: tail) (pre.length + 1) (if keep then out ++ [bit] else out)) := by
  simp [step, machine, config, Configuration.scanned, Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; cases keep <;> fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; cases keep <;> fin_cases i <;> simp [applyAction, action, Streaming.write_append]

theorem skip_marker (keep : Bool) (pre tail out : List Bool) :
    step (machine keep) (config 2 (pre ++ true :: tail) pre.length out) =
      some (config 3 (pre ++ true :: tail) (pre.length + 1) out) := by
  simp [step, machine, config, Configuration.scanned, Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem skip_bit (keep : Bool) (source out : List Bool) (pos : ℕ) :
    step (machine keep) (config 3 source pos out) = some (config 2 source (pos + 1) out) := by
  simp [step, machine, config]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem skip_end (keep : Bool) (pre tail out : List Bool) :
    step (machine keep) (config 2 (pre ++ false :: tail) pre.length out) =
      some (config 4 (pre ++ false :: tail) (pre.length + 1) out) := by
  simp [step, machine, config, Configuration.scanned, Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem skip_prefix (keep : Bool) (pre bits suffix out : List Bool) :
    Prefix (machine keep) ((pre ++ frame bits ++ suffix).length + out.length) (2 * bits.length + 1)
      (config 2 (pre ++ frame bits ++ suffix) pre.length out)
      (config 4 (pre ++ frame bits ++ suffix) (pre.length + 2 * bits.length + 1) out) := by
  induction bits generalizing pre with
  | nil =>
    simpa [frame] using Prefix.step
      (by simp : (config 2 (pre ++ false :: suffix) pre.length out).tapeCells ≤ (pre ++ false :: suffix).length + out.length)
      (by rfl : (machine keep).halted (2 : Fin 5) = false) (skip_end keep pre suffix out)
      (Prefix.refl _ (by simp))
  | cons bit bits ih =>
    let source := pre ++ frame (bit :: bits) ++ suffix
    let space := source.length + out.length
    have he : (pre ++ [true, bit]) ++ frame bits ++ suffix = source := by simp [source, frame, List.append_assoc]
    have ht : Prefix (machine keep) space (2 * bits.length + 1)
        (config 2 source (pre.length + 2) out)
        (config 4 source (pre.length + 2 * (bit :: bits).length + 1) out) := by
      have h := ih (pre ++ [true, bit])
      rw [he] at h
      have hlen : (pre ++ [true, bit]).length = pre.length + 2 := by simp
      have hpos : pre.length + 2 + 2 * bits.length + 1 = pre.length + 2 * (bit :: bits).length + 1 := by simp; omega
      rw [hlen, hpos] at h
      exact h
    have h1 := Prefix.step (by simp [space] : (config 3 source (pre.length + 1) out).tapeCells ≤ space)
      (by rfl : (machine keep).halted (3 : Fin 5) = false) (skip_bit keep source out (pre.length + 1))
      (by simpa [Nat.add_assoc] using ht)
    have h0 := Prefix.step (by simp [space] : (config 2 source pre.length out).tapeCells ≤ space)
      (by rfl : (machine keep).halted (2 : Fin 5) = false)
      (by simpa [source, frame, List.append_assoc] using skip_marker keep pre (bit :: frame bits ++ suffix) out) h1
    have htime : 2 * bits.length + 1 + 1 + 1 = 2 * (bit :: bits).length + 1 := by simp; omega
    rw [htime] at h0
    exact h0

theorem cell_run (keep bit : Bool) (pre keys suffix out : List Bool) :
    ∃ r : ExecutionReceipt 2 5,
      runFrom (machine keep) (2 * keys.length + 3)
        (config 0 (pre ++ frame (bit :: keys) ++ suffix) pre.length out) = some r ∧
      r.final = config 4 (pre ++ frame (bit :: keys) ++ suffix) (pre.length + 2 * keys.length + 3)
        (if keep then out ++ [bit] else out) ∧
      r.steps = 2 * keys.length + 3 ∧
      r.peakTapeCells ≤ (pre ++ frame (bit :: keys) ++ suffix).length + out.length + 1 := by
  let source := pre ++ frame (bit :: keys) ++ suffix
  let appended := if keep then out ++ [bit] else out
  let space := source.length + out.length + 1
  have he : (pre ++ [true, bit]) ++ frame keys ++ suffix = source := by simp [source, frame, List.append_assoc]
  have hp := skip_prefix keep (pre ++ [true, bit]) keys suffix appended
  rw [he] at hp
  have ht : Prefix (machine keep) space (2 * keys.length + 1)
      (config 2 source (pre.length + 2) appended) (config 4 source (pre.length + 2 * keys.length + 3) appended) := by
    have h := hp.enlarge (large := space) (by cases keep <;> simp [space, appended]; omega)
    have hlen : (pre ++ [true, bit]).length = pre.length + 2 := by simp
    have hpos : pre.length + 2 + 2 * keys.length + 1 = pre.length + 2 * keys.length + 3 := by omega
    rw [hlen, hpos] at h
    exact h
  have hb : step (machine keep) (config 1 source (pre.length + 1) out) =
      some (config 2 source (pre.length + 2) appended) := by
    simpa [source, frame, appended, List.append_assoc] using payload_step keep bit (pre ++ [true]) (frame keys ++ suffix) out
  have h1 := Prefix.step (by simp [space] : (config 1 source (pre.length + 1) out).tapeCells ≤ space)
    (by rfl : (machine keep).halted (1 : Fin 5) = false) hb ht
  have h0 := Prefix.step (by simp [space] : (config 0 source pre.length out).tapeCells ≤ space)
    (by rfl : (machine keep).halted (0 : Fin 5) = false)
    (by simpa [source, frame, List.append_assoc] using marker_step keep pre (bit :: frame keys ++ suffix) out) h1
  obtain ⟨r, hr, hf, hs, hpeak⟩ := h0.run (by rfl) (by cases keep <;> simp [space, appended]; omega)
  exact ⟨r, by simpa [source, Nat.add_assoc] using hr, hf, by omega, hpeak⟩

end NearCubicWires.RepairOrdinary.PayloadField
