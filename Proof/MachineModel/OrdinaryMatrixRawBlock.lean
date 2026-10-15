import Proof.MachineModel.OrdinaryUnaryTemplate

/-! Sequential raw-bit selection for the Williams crop. The block length
is read from a physical unary template, which is reset for the next cell.
The source and growing output cursors retain their streaming endpoints. -/
namespace NearCubicWires.RepairOrdinary.MatrixRawBlock
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {s : ℕ} (state : Fin s) (driver : List Bool) (head : ℕ)
    (source : List Bool) (pos : ℕ) (out : List Bool) : Configuration 3 s :=
  ⟨state, ![head, pos, out.length], ![driver, source, out]⟩

@[simp] theorem config_cells {s : ℕ} (state : Fin s) (driver : List Bool) (head : ℕ)
    (source : List Bool) (pos : ℕ) (out : List Bool) :
    (config state driver head source pos out).tapeCells = driver.length + source.length + out.length := by
  simp [config, Configuration.tapeCells, Fin.sum_univ_succ, Nat.add_assoc]

def selected (keep : Bool) (bits : List Bool) : List Bool := if keep then bits else []

def copy (keep : Bool) : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 1
  rule := fun state scanned => if state.val = 0 then
    some (if scanned 0 then
      ⟨0, ![none, none, if keep then some (scanned 1) else none],
        ![.right, .right, if keep then .right else .stay]⟩
    else ⟨1, ![none, none, none], ![.stay, .stay, .stay]⟩)
    else none

theorem emit_step (keep bit : Bool) (driver : List Bool) (head : ℕ)
    (pre tail out : List Bool) (hmark : readTapeBit driver head = true) :
    step (copy keep) (config 0 driver head (pre ++ bit :: tail) pre.length out) =
      some (config 0 driver (head + 1) (pre ++ bit :: tail) (pre.length + 1)
        (out ++ selected keep [bit])) := by
  simp [step, copy, config, Configuration.scanned, hmark, Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; cases keep <;> fin_cases i <;> simp [applyAction, HeadMove.apply, selected]
  · funext i; cases keep <;> fin_cases i <;> simp [applyAction, Streaming.write_append, selected]

theorem stop_step (keep : Bool) (driver : List Bool) (head : ℕ)
    (source out : List Bool) (pos : ℕ) (hend : readTapeBit driver head = false) :
    step (copy keep) (config 0 driver head source pos out) =
      some (config 1 driver head source pos out) := by
  simp [step, copy, config, Configuration.scanned, hend]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem copy_prefix (keep : Bool) (pre bits suffix out : List Bool) (processed count : ℕ)
    (hc : processed + bits.length = count) :
    Prefix (copy keep) (count + 2 + (pre ++ bits ++ suffix).length + out.length + bits.length)
      (bits.length + 1)
      (config 0 (UnaryTemplate.tape count) (processed + 1) (pre ++ bits ++ suffix) pre.length out)
      (config 1 (UnaryTemplate.tape count) (count + 1) (pre ++ bits ++ suffix)
        (pre.length + bits.length) (out ++ selected keep bits)) := by
  induction bits generalizing pre out processed with
  | nil =>
    have he : processed = count := by simpa using hc
    subst processed
    simpa [selected] using Prefix.step
      (by simp : (config (s := 2) 0 (UnaryTemplate.tape count) (count + 1) (pre ++ suffix) pre.length out).tapeCells ≤
        count + 2 + (pre ++ suffix).length + out.length)
      (by rfl : (copy keep).halted 0 = false)
      (stop_step keep (UnaryTemplate.tape count) (count + 1) (pre ++ suffix) out pre.length (UnaryTemplate.tape_end count))
      (Prefix.refl _ (by simp))
  | cons bit bits ih =>
    let source := pre ++ (bit :: bits) ++ suffix
    let appended := out ++ selected keep [bit]
    have hsource : (pre ++ [bit]) ++ bits ++ suffix = source := by simp [source, List.append_assoc]
    have hout : appended ++ selected keep bits = out ++ selected keep (bit :: bits) := by
      cases keep <;> simp [appended, selected, List.append_assoc]
    have hpos : (pre ++ [bit]).length + bits.length = pre.length + (bit :: bits).length := by simp; omega
    have happ : appended.length ≤ out.length + 1 := by cases keep <;> simp [appended, selected]
    have hp := ih (pre ++ [bit]) appended (processed + 1) (by simp only [List.length_cons] at hc; omega)
    rw [hsource, hout, hpos] at hp
    have ht := hp.enlarge (large := count + 2 + source.length + out.length + (bit :: bits).length)
      (by simp only [List.length_cons]; omega)
    have hlen : (pre ++ [bit]).length = pre.length + 1 := by simp
    rw [hlen] at ht
    have hmark := UnaryTemplate.tape_mark count processed (by simp only [List.length_cons] at hc; omega)
    have hs : step (copy keep) (config 0 (UnaryTemplate.tape count) (processed + 1) source pre.length out) =
        some (config 0 (UnaryTemplate.tape count) (processed + 2) source (pre.length + 1) appended) := by
      simpa [source, appended, List.cons_append, Nat.add_assoc] using
        emit_step keep bit (UnaryTemplate.tape count) (processed + 1) pre (bits ++ suffix) out hmark
    have hj := Prefix.step
      (by simp : (config (s := 2) 0 (UnaryTemplate.tape count) (processed + 1) source pre.length out).tapeCells ≤
        count + 2 + source.length + out.length + (bit :: bits).length)
      (by rfl : (copy keep).halted 0 = false) hs (by simpa only [Nat.add_assoc] using ht)
    exact hj

def reset : Machine 3 3 := TapeEmbedding.machine 2 UnaryTemplate.machine
def machine (keep : Bool) : Machine 3 5 := Composition.machine (copy keep) reset

theorem place (state : Fin 3) (count head : ℕ) (source out : List Bool) (pos : ℕ) :
    TapeEmbedding.config ![pos, out.length] ![source, out]
      (UnaryTemplate.config state (UnaryTemplate.tape count) head) =
      config state (UnaryTemplate.tape count) head source pos out := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [TapeEmbedding.config, UnaryTemplate.config, config, Fin.addCases]
  · funext i; fin_cases i <;> simp [TapeEmbedding.config, UnaryTemplate.config, config, Fin.addCases]

theorem block_run (keep : Bool) (pre bits suffix out : List Bool) :
    ∃ r : ExecutionReceipt 3 5,
      runFrom (machine keep) (2 * bits.length + 4)
        (config 0 (UnaryTemplate.tape bits.length) 1 (pre ++ bits ++ suffix) pre.length out) = some r ∧
      r.final = config 4 (UnaryTemplate.tape bits.length) 1 (pre ++ bits ++ suffix)
        (pre.length + bits.length) (out ++ selected keep bits) ∧
      r.steps = 2 * bits.length + 4 ∧
      r.peakTapeCells ≤ (pre ++ bits ++ suffix).length + out.length + 2 * bits.length + 2 := by
  have hp := copy_prefix keep pre bits suffix out 0 bits.length (by simp)
  have hsel : (selected keep bits).length ≤ bits.length := by cases keep <;> simp [selected]
  obtain ⟨first, hr, hf, hs, hpeak⟩ := hp.run (by rfl)
    (by simp only [config_cells, UnaryTemplate.tape_length, List.length_append]; omega)
  obtain ⟨second, hrun, hfinal, hsteps, hb⟩ := UnaryTemplate.reset_run bits.length
  let source := pre ++ bits ++ suffix
  let appended := out ++ selected keep bits
  let next := pre.length + bits.length
  have he := TapeEmbedding.run_embed UnaryTemplate.machine ![next, appended.length] ![source, appended] _ _ second hrun
  have hmid : Composition.restart first.final reset.start =
      config 0 (UnaryTemplate.tape bits.length) (bits.length + 1) source next appended := by rw [hf]; rfl
  have he' : runFrom reset (bits.length + 2) (Composition.restart first.final reset.start) =
      some (TapeEmbedding.receipt ![next, appended.length] ![source, appended] second) := by
    rw [hmid]
    simpa only [place, reset] using he
  have hj := Composition.run_join (copy keep) reset (bits.length + 1) (bits.length + 2) _ first _ hr he'
  refine ⟨Composition.joinedReceipt first (TapeEmbedding.receipt ![next, appended.length] ![source, appended] second), ?_, ?_, ?_, ?_⟩
  · have heq : bits.length + 1 + 1 + (bits.length + 2) = 2 * bits.length + 4 := by omega
    rw [heq] at hj
    exact hj
  · change Composition.rightConfig 2 (TapeEmbedding.config ![next, appended.length] ![source, appended] second.final) = _
    rw [hfinal, place]
    rfl
  · change first.steps + 1 + second.steps = _
    omega
  · change max first.peakTapeCells (second.peakTapeCells + TapeEmbedding.extraCells ![source, appended]) ≤ _
    simp only [TapeEmbedding.extraCells, Fin.sum_univ_succ] at *
    simp only [MatrixRawBlock.selected, source, appended, List.length_append] at *
    cases keep <;> simp_all <;> omega

end NearCubicWires.RepairOrdinary.MatrixRawBlock
