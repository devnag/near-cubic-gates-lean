import Proof.MachineModel.OrdinaryBucketScan

/-! Locate the rank half of a bounded annotated record. Two already loaded
copies permit a four-to-two physical-head walk, without a numeric-width
oracle or any reread of the surrounding table. Loading the copies is charged
by the caller. -/
namespace NearCubicWires.RepairOrdinary.HalfPosition
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (state : Fin 5) (fast slow : HeadMove) : Action 2 5 := ⟨state, fun _ => none, ![fast, slow]⟩
def machine : Machine 2 5 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 4
  rule := fun state scanned => if state.val = 0 then
      some (if scanned 0 then action 1 .right .stay else action 4 .stay .stay)
    else if state.val = 1 then some (action 2 .right .right)
    else if state.val = 2 then some (action 3 .right .stay)
    else if state.val = 3 then some (action 0 .right .right)
    else none
def config (state : Fin 5) (fast slow : List Bool) (fastHead slowHead : ℕ) : Configuration 2 5 :=
  ⟨state, ![fastHead, slowHead], ![fast, slow]⟩
@[simp] theorem config_cells (state : Fin 5) (fast slow : List Bool) (fastHead slowHead : ℕ) :
    (config state fast slow fastHead slowHead).tapeCells = fast.length + slow.length := by
  simp [config, Configuration.tapeCells, Fin.sum_univ_succ]

theorem first_step (fast slow : List Bool) (fastHead slowHead : ℕ) (hr : readTapeBit fast fastHead = true) :
    step machine (config 0 fast slow fastHead slowHead) = some (config 1 fast slow (fastHead + 1) slowHead) := by
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · rfl

theorem next_step (fast slow : List Bool) (fastHead slowHead : ℕ) (phase : Fin 3) :
    step machine (config ⟨phase.val + 1, by omega⟩ fast slow fastHead slowHead) =
      some (config (if phase.val = 2 then 0 else ⟨phase.val + 2, by omega⟩) fast slow (fastHead + 1)
        (slowHead + if phase.val = 1 then 0 else 1)) := by
  fin_cases phase <;> simp [step, machine, config] <;> apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply])

theorem stop_step (fast slow : List Bool) (fastHead slowHead : ℕ) (hr : readTapeBit fast fastHead = false) :
    step machine (config 0 fast slow fastHead slowHead) = some (config 4 fast slow fastHead slowHead) := by
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · rfl

theorem cycle_prefix (fast slow : List Bool) (fastHead slowHead : ℕ) (hr : readTapeBit fast fastHead = true) :
    Prefix machine (fast.length + slow.length) 4 (config 0 fast slow fastHead slowHead)
      (config 0 fast slow (fastHead + 4) (slowHead + 2)) := by
  have h3 := Prefix.step (by simp : (config 3 fast slow (fastHead + 3) (slowHead + 1)).tapeCells ≤ fast.length + slow.length)
    (by rfl : machine.halted (3 : Fin 5) = false) (next_step fast slow (fastHead + 3) (slowHead + 1) 2)
    (Prefix.refl _ (by simp))
  have h2 := Prefix.step (by simp : (config 2 fast slow (fastHead + 2) (slowHead + 1)).tapeCells ≤ fast.length + slow.length)
    (by rfl : machine.halted (2 : Fin 5) = false) (next_step fast slow (fastHead + 2) (slowHead + 1) 1)
    (by simpa [Nat.add_assoc] using h3)
  have h1 := Prefix.step (by simp : (config 1 fast slow (fastHead + 1) slowHead).tapeCells ≤ fast.length + slow.length)
    (by rfl : machine.halted (1 : Fin 5) = false) (next_step fast slow (fastHead + 1) slowHead 0)
    (by simpa [Nat.add_assoc] using h2)
  have h0 := Prefix.step (by simp : (config 0 fast slow fastHead slowHead).tapeCells ≤ fast.length + slow.length)
    (by rfl : machine.halted (0 : Fin 5) = false) (first_step fast slow fastHead slowHead hr)
    (by simpa [Nat.add_assoc] using h1)
  simpa [Nat.add_assoc] using h0

theorem even_prefix (n : ℕ) (pre bits suffix slow : List Bool) (slowHead : ℕ) (hlen : bits.length = 2 * n) :
    Prefix machine ((pre ++ frame bits ++ suffix).length + slow.length) (4 * n + 1)
      (config 0 (pre ++ frame bits ++ suffix) slow pre.length slowHead)
      (config 4 (pre ++ frame bits ++ suffix) slow (pre.length + 4 * n) (slowHead + 2 * n)) := by
  induction n generalizing pre bits slowHead with
  | zero =>
    have hz : bits = [] := List.length_eq_zero_iff.mp (by omega)
    subst bits
    have hread : readTapeBit (pre ++ frame [] ++ suffix) pre.length = false := by
      simpa [frame] using Streaming.read_append pre suffix false
    have hp := Prefix.step (by simp : (config 0 (pre ++ frame [] ++ suffix) slow pre.length slowHead).tapeCells ≤
      (pre ++ frame [] ++ suffix).length + slow.length) (by rfl : machine.halted (0 : Fin 5) = false)
      (stop_step _ _ _ _ hread) (Prefix.refl _ (by simp))
    simpa using hp
  | succ n ih =>
    cases bits with
    | nil => simp at hlen
    | cons first bits =>
      cases bits with
      | nil => simp at hlen; omega
      | cons second bits =>
        have htlen : bits.length = 2 * n := by simp only [List.length_cons] at hlen; omega
        let fast := pre ++ frame (first :: second :: bits) ++ suffix
        have he : (pre ++ [true, first, true, second]) ++ frame bits ++ suffix = fast := by
          simp [fast, frame, List.append_assoc]
        have hread : readTapeBit fast pre.length = true := by
          simpa [fast, frame, List.append_assoc] using
            Streaming.read_append pre (first :: true :: second :: frame bits ++ suffix) true
        have hp := cycle_prefix fast slow pre.length slowHead hread
        have ht := ih (pre ++ [true, first, true, second]) bits (slowHead + 2) htlen
        rw [he] at ht
        have ht' : Prefix machine (fast.length + slow.length) (4 * n + 1)
            (config 0 fast slow (pre.length + 4) (slowHead + 2))
            (config 4 fast slow (pre.length + 4 * (n + 1)) (slowHead + 2 * (n + 1))) := by
          simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
        have hj := hp.trans ht'
        convert hj using 1
        omega

theorem annotated_run (word rank : List Bool) (hw : rank.length = word.length) :
    ∃ r : ExecutionReceipt 2 5,
      runFrom machine (4 * word.length + 1) (config 0 (frame (word ++ rank)) (frame (word ++ rank)) 0 0) = some r ∧
      r.final = config 4 (frame (word ++ rank)) (frame (word ++ rank)) (4 * word.length) (2 * word.length) ∧
      r.steps = 4 * word.length + 1 ∧ r.peakTapeCells ≤ 8 * word.length + 2 := by
  have hp := even_prefix word.length [] (word ++ rank) [] (frame (word ++ rank)) 0 (by simp [hw]; omega)
  obtain ⟨r, hr, hf, hs, hpeak⟩ := hp.run (by rfl) (by simp)
  refine ⟨r, by simpa using hr, by simpa using hf, hs, ?_⟩
  simp only [List.nil_append, List.append_nil, frame_length, List.length_append, hw] at hpeak
  omega

end NearCubicWires.RepairOrdinary.HalfPosition
