import Proof.MachineModel.OrdinaryUnaryTemplate

/-! Actual dimension-counted payload traversal. A unary template controls the
number of records, so the row boundary needs no delimiter or coordinate test. -/
namespace NearCubicWires.RepairOrdinary.PayloadCounted
open LocalBitMultitape StablePartition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def family (keep : Bool) : Bool → Machine 2 5 := fun _ => PayloadField.machine keep
def machine (keep : Bool) : Machine 3 14 := UnaryController.machine (family keep)
def config {s : ℕ} (state : Fin s) (source : List Bool) (pos : ℕ) (out : List Bool)
    (driverHead : ℕ) (driver : List Bool) : Configuration 3 s :=
  TapeEmbedding.config (fun _ : Fin 1 => driverHead) (fun _ : Fin 1 => driver)
    ⟨state, ![pos, out.length], ![source, out]⟩
def selected (keep : Bool) (records : List Record) : List Bool := if keep then records.map Prod.fst else []
@[simp] theorem selected_length (keep : Bool) (records : List Record) : (selected keep records).length ≤ records.length := by
  cases keep <;> simp [selected]
@[simp] theorem selected_cons (keep : Bool) (r : Record) (records : List Record) :
    selected keep (r :: records) = (if keep then [r.1] else []) ++ selected keep records := by cases keep <;> rfl
@[simp] theorem config_cells {s : ℕ} (state : Fin s) (source : List Bool) (pos : ℕ) (out : List Bool)
    (driverHead : ℕ) (driver : List Bool) : (config state source pos out driverHead driver).tapeCells =
      source.length + out.length + driver.length := by
  simp [config, TapeEmbedding.config, Configuration.tapeCells, Fin.sum_univ_succ, Fin.addCases, Nat.add_assoc]

theorem loop_prefix (keep phase : Bool) (pre : List Bool) (records : List Record) (suffix out : List Bool)
    (processed count : ℕ) (hcount : processed + records.length = count) :
    ∃ finalPhase,
      Prefix (machine keep) ((pre ++ recordsBits records ++ suffix).length + out.length + records.length + count + 2)
        ((recordsBits records).length + 2 * records.length + 1)
        (config (UnaryController.test (s := 5) phase) (pre ++ recordsBits records ++ suffix) pre.length out
          (processed + 1) (UnaryTemplate.tape count))
        (config (UnaryController.stop (s := 5) finalPhase) (pre ++ recordsBits records ++ suffix)
          (pre.length + (recordsBits records).length) (out ++ selected keep records)
          (count + 1) (UnaryTemplate.tape count)) := by
  induction records generalizing phase pre out processed with
  | nil =>
    have he : processed = count := by simpa using hcount
    subst processed
    let source := pre ++ suffix
    have hs := UnaryController.stop_step (family keep) phase ![pre.length, out.length] ![source, out]
      (count + 1) (UnaryTemplate.tape count) (UnaryTemplate.tape_end count)
    change step (machine keep)
      (config (UnaryController.test (s := 5) phase) source pre.length out (count + 1) (UnaryTemplate.tape count)) =
        some (config (UnaryController.stop (s := 5) phase) source pre.length out (count + 1) (UnaryTemplate.tape count)) at hs
    have hp : Prefix (machine keep) (source.length + out.length + count + 2) 1
        (config (UnaryController.test (s := 5) phase) source pre.length out (count + 1) (UnaryTemplate.tape count))
        (config (UnaryController.stop (s := 5) phase) source pre.length out (count + 1) (UnaryTemplate.tape count)) :=
      Prefix.step (by simp; omega) (UnaryController.test_halted _ _) hs (Prefix.refl _ (by simp; omega))
    exact ⟨phase, by simpa [recordsBits, selected, source] using hp⟩
  | cons entry records ih =>
    rcases entry with ⟨bit, keys⟩
    let stored := frame (bit :: keys)
    let source := pre ++ recordsBits ((bit, keys) :: records) ++ suffix
    let driver := UnaryTemplate.tape count
    let next := pre.length + 2 * keys.length + 3
    let appended := if keep then out ++ [bit] else out
    let space := source.length + out.length + (records.length + 1) + count + 2
    have hstored : stored.length = 2 * keys.length + 3 := by simp [stored]; omega
    have happ : appended.length ≤ out.length + 1 := by cases keep <;> simp [appended]
    have hsource : (pre ++ stored) ++ recordsBits records ++ suffix = source := by
      simp [source, stored, recordsBits, recordBits, frame, List.append_assoc]
    have hnext : (pre ++ stored).length = next := by simp [next, hstored, Nat.add_assoc]
    obtain ⟨body, hbody, hbf, hbs, hbp⟩ := PayloadField.cell_run keep bit pre keys (recordsBits records ++ suffix) out
    have hsource' : pre ++ frame (bit :: keys) ++ (recordsBits records ++ suffix) = source := by
      simpa only [stored, List.append_assoc] using hsource
    rw [hsource'] at hbody hbf hbp
    obtain ⟨finalPhase, tailPrefix⟩ := ih (!phase) (pre ++ stored) appended (processed + 1) (by simp only [List.length_cons] at hcount; omega)
    rw [hsource] at tailPrefix
    have tailPrefix' : Prefix (machine keep) space ((recordsBits records).length + 2 * records.length + 1)
        (config (UnaryController.test (s := 5) (!phase)) source next appended (processed + 2) driver)
        (config (UnaryController.stop (s := 5) finalPhase) source
          (pre.length + (recordsBits ((bit, keys) :: records)).length) (out ++ selected keep ((bit, keys) :: records))
          (count + 1) driver) := by
      have ht := tailPrefix.enlarge (large := space) (by dsimp only [space]; omega)
      have hfields : (recordsBits ((bit, keys) :: records)).length = stored.length + (recordsBits records).length := by
        simp only [recordsBits, List.flatMap_cons, List.length_append]
        rfl
      have hend : (pre ++ stored).length + (recordsBits records).length =
          pre.length + (recordsBits ((bit, keys) :: records)).length := by rw [List.length_append, hfields]; omega
      have hout : appended ++ selected keep records = out ++ selected keep ((bit, keys) :: records) := by
        cases keep <;> simp [appended, selected, List.append_assoc]
      rw [hend, hnext, hout] at ht
      simpa only [Nat.add_assoc] using ht
    obtain ⟨bp, halted⟩ := UnaryController.body_prefix (family keep) phase _ _ body hbody (processed + 2) driver
    have bp' : Prefix (machine keep) space body.steps
        (controlConfig (UnaryController.code (s := 5) phase) (config (0 : Fin 5) source pre.length out (processed + 2) driver))
        (controlConfig (UnaryController.code (s := 5) phase) (config (4 : Fin 5) source next appended (processed + 2) driver)) := by
      have h := bp.enlarge (large := space) (by dsimp only [space, driver]; rw [UnaryTemplate.tape_length]; omega)
      rw [hbf] at h
      exact h
    have hend : (config (UnaryController.test (s := 5) (!phase)) source next appended (processed + 2) driver).tapeCells ≤ space := by
      simp only [config_cells]
      dsimp only [space, driver]
      rw [UnaryTemplate.tape_length]
      omega
    have hreturn : step (machine keep)
        (controlConfig (UnaryController.code (s := 5) phase) (config (4 : Fin 5) source next appended (processed + 2) driver)) =
        some (config (UnaryController.test (s := 5) (!phase)) source next appended (processed + 2) driver) := by
      have h := UnaryController.return_step (family keep) phase body.final (processed + 2) driver halted
      rw [hbf] at h
      exact h
    have hbodyEnd : (controlConfig (UnaryController.code (s := 5) phase)
        (config (4 : Fin 5) source next appended (processed + 2) driver)).tapeCells ≤ space := hend
    have returned := Prefix.step hbodyEnd (UnaryController.body_halted _ _ _) hreturn tailPrefix'
    have hread : readTapeBit driver (processed + 1) = true :=
      UnaryTemplate.tape_mark count processed (by simp only [List.length_cons] at hcount; omega)
    have henter : step (machine keep)
        (config (UnaryController.test (s := 5) phase) source pre.length out (processed + 1) driver) =
        some (controlConfig (UnaryController.code (s := 5) phase) (config (0 : Fin 5) source pre.length out (processed + 2) driver)) :=
      UnaryController.enter_step (family keep) phase ![pre.length, out.length] ![source, out] (processed + 1) driver hread
    have hstart : (config (UnaryController.test (s := 5) phase) source pre.length out (processed + 1) driver).tapeCells ≤ space := by
      simp only [config_cells]
      dsimp only [space, driver]
      rw [UnaryTemplate.tape_length]
      omega
    have joined := Prefix.step hstart (UnaryController.test_halted _ _) henter (bp'.trans returned)
    have htime : body.steps + ((recordsBits records).length + 2 * records.length + 1 + 1) + 1 =
        (recordsBits ((bit, keys) :: records)).length + 2 * ((bit, keys) :: records).length + 1 := by
      simp only [recordsBits, List.flatMap_cons, List.length_append, List.length_cons]
      change body.steps + ((recordsBits records).length + 2 * records.length + 1 + 1) + 1 =
        (frame (bit :: keys)).length + (recordsBits records).length + 2 * (records.length + 1) + 1
      rw [frame_length]
      simp only [List.length_cons]
      omega
    rw [htime] at joined
    exact ⟨finalPhase, joined⟩

theorem loop_run (keep : Bool) (pre : List Bool) (records : List Record) (suffix out : List Bool) :
    ∃ finalPhase, ∃ r : ExecutionReceipt 3 14,
      runFrom (machine keep) ((recordsBits records).length + 2 * records.length + 1)
        (config (UnaryController.test (s := 5) false) (pre ++ recordsBits records ++ suffix) pre.length out
          1 (UnaryTemplate.tape records.length)) = some r ∧
      r.final = config (UnaryController.stop (s := 5) finalPhase) (pre ++ recordsBits records ++ suffix)
        (pre.length + (recordsBits records).length) (out ++ selected keep records)
          (records.length + 1) (UnaryTemplate.tape records.length) ∧
      r.steps = (recordsBits records).length + 2 * records.length + 1 ∧
      r.peakTapeCells ≤ (pre ++ recordsBits records ++ suffix).length + out.length + 2 * records.length + 2 := by
  obtain ⟨phase, hp⟩ := loop_prefix keep false pre records suffix out 0 records.length (by simp)
  have hsel := selected_length keep records
  obtain ⟨r, hr, hf, hs, hb⟩ := hp.run (UnaryController.stop_halted (family keep) phase)
    (by simp only [config_cells, List.length_append, UnaryTemplate.tape_length]; omega)
  exact ⟨phase, r, hr, hf, hs, by omega⟩

end NearCubicWires.RepairOrdinary.PayloadCounted
