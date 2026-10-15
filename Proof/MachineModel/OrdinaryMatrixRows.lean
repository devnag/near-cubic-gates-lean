import Proof.MachineModel.OrdinaryPaddedRow

/-! A fixed outer row controller executes the padded-row body with reused
dimension templates. Every row and control transition is charged. -/
namespace NearCubicWires.RepairOrdinary.MatrixRows
open LocalBitMultitape
open StablePartition (Record recordsBits)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def family : Bool → Machine 4 22 := fun _ => PaddedRow.machine
def machine : Machine 5 48 := UnaryController.machine family
def fields (rows : List (List Record)) : List Bool := rows.flatMap recordsBits
def output (pad : ℕ) (rows : List (List Record)) : List Bool :=
  rows.flatMap (fun row => row.map Prod.fst ++ List.replicate pad false)
def config {s : ℕ} (state : Fin s) (source : List Bool) (pos : ℕ) (out : List Bool)
    (used pad head count : ℕ) : Configuration 5 s :=
  TapeEmbedding.config (fun _ : Fin 1 => head) (fun _ : Fin 1 => UnaryTemplate.tape count)
    (PaddedRow.config state source pos out used pad)
@[simp] theorem config_cells {s : ℕ} (state : Fin s) (source : List Bool) (pos : ℕ)
    (out : List Bool) (used pad head count : ℕ) :
    (config state source pos out used pad head count).tapeCells = source.length + out.length + used + pad + count + 6 := by
  simp [config, TapeEmbedding.config_cells, TapeEmbedding.extraCells]
  omega

theorem output_length (pad used : ℕ) (rows : List (List Record))
    (hw : ∀ row ∈ rows, row.length = used) : (output pad rows).length = rows.length * (used + pad) := by
  induction rows with
  | nil => simp [output]
  | cons row rows ih =>
    have hr := hw row (by simp)
    have ht := ih (fun r h => hw r (by simp [h]))
    simp only [output, List.flatMap_cons, List.length_append, List.length_map, List.length_replicate,
      List.length_cons] at ht ⊢
    rw [hr, ht]
    rw [Nat.add_mul]
    omega

theorem loop_prefix (phase : Bool) (pre : List Bool) (rows : List (List Record)) (suffix out : List Bool)
    (used pad processed count : ℕ) (hw : ∀ row ∈ rows, row.length = used)
    (hcount : processed + rows.length = count) :
    ∃ finalPhase,
      Prefix machine ((pre ++ fields rows ++ suffix).length + out.length + (rows.length + 2) * (used + pad) + count + 6)
        ((fields rows).length + rows.length * (3 * used + 2 * pad + 11) + 1)
        (config (UnaryController.test (s := 22) phase) (pre ++ fields rows ++ suffix) pre.length out
          used pad (processed + 1) count)
        (config (UnaryController.stop (s := 22) finalPhase) (pre ++ fields rows ++ suffix)
          (pre.length + (fields rows).length) (out ++ output pad rows) used pad (count + 1) count) := by
  induction rows generalizing phase pre out processed with
  | nil =>
    have he : processed = count := by simpa using hcount
    subst processed
    let source := pre ++ suffix
    let core := PaddedRow.config PaddedRow.machine.start source pre.length out used pad
    have hs := UnaryController.stop_step family phase core.heads core.tapes
      (count + 1) (UnaryTemplate.tape count) (UnaryTemplate.tape_end count)
    change step machine (config (UnaryController.test (s := 22) phase) source pre.length out used pad (count + 1) count) =
      some (config (UnaryController.stop (s := 22) phase) source pre.length out used pad (count + 1) count) at hs
    have hp := Prefix.step
      (by simp; omega : (config (UnaryController.test (s := 22) phase) source pre.length out used pad (count + 1) count).tapeCells ≤
        source.length + out.length + 2 * (used + pad) + count + 6)
      (UnaryController.test_halted family phase) hs (Prefix.refl _ (by simp; omega))
    exact ⟨phase, by simpa [fields, output, source, machine] using hp⟩
  | cons row rows ih =>
    have hrow := hw row (by simp)
    have hrows : ∀ r ∈ rows, r.length = used := fun r h => hw r (by simp [h])
    let source := pre ++ fields (row :: rows) ++ suffix
    let next := pre.length + (recordsBits row).length
    let appended := out ++ row.map Prod.fst ++ List.replicate pad false
    let space := source.length + out.length + (rows.length + 3) * (used + pad) + count + 6
    let driver := UnaryTemplate.tape count
    have happ : appended.length = out.length + (used + pad) := by simp [appended, hrow]
    have hsource : (pre ++ recordsBits row) ++ fields rows ++ suffix = source := by
      simp [source, fields, List.append_assoc]
    have hnext : (pre ++ recordsBits row).length = next := by simp [next]
    have hfields : (fields (row :: rows)).length = (recordsBits row).length + (fields rows).length := by
      simp [fields]
    obtain ⟨body, hbody, hbf, hbs, hbp⟩ := PaddedRow.row_run pre row (fields rows ++ suffix) out pad
    have hsource' : pre ++ recordsBits row ++ (fields rows ++ suffix) = source := by
      simpa only [List.append_assoc] using hsource
    rw [hsource'] at hbody hbf hbp
    rw [hrow] at hbody hbf hbp hbs
    obtain ⟨finalPhase, tailPrefix⟩ := ih (!phase) (pre ++ recordsBits row) appended (processed + 1) hrows
      (by simp only [List.length_cons] at hcount; omega)
    rw [hsource] at tailPrefix
    have tailPrefix' : Prefix machine space ((fields rows).length + rows.length * (3 * used + 2 * pad + 11) + 1)
        (config (UnaryController.test (s := 22) (!phase)) source next appended used pad (processed + 2) count)
        (config (UnaryController.stop (s := 22) finalPhase) source
          (pre.length + (fields (row :: rows)).length) (out ++ output pad (row :: rows)) used pad (count + 1) count) := by
      have ht := tailPrefix.enlarge (large := space) (by dsimp only [space]; rw [happ]; simp only [Nat.add_mul]; omega)
      have hend : (pre ++ recordsBits row).length + (fields rows).length = pre.length + (fields (row :: rows)).length := by
        rw [List.length_append, hfields]; omega
      have hout : appended ++ output pad rows = out ++ output pad (row :: rows) := by
        simp [appended, output, List.append_assoc]
      rw [hend, hnext, hout] at ht
      simpa only [Nat.add_assoc] using ht
    obtain ⟨bp, halted⟩ := UnaryController.body_prefix family phase _ _ body hbody (processed + 2) driver
    have bp' : Prefix machine space body.steps
        (controlConfig (UnaryController.code (s := 22) phase)
          (config PaddedRow.machine.start source pre.length out used pad (processed + 2) count))
        (controlConfig (UnaryController.code (s := 22) phase)
          (config (21 : Fin 22) source next appended used pad (processed + 2) count)) := by
      have h := bp.enlarge (large := space) (by
        dsimp only [space, driver]
        rw [UnaryTemplate.tape_length]
        have hn : 2 * (used + pad) ≤ (rows.length + 3) * (used + pad) := Nat.mul_le_mul_right _ (by omega)
        omega)
      rw [hbf] at h
      exact h
    have hend : (config (UnaryController.test (s := 22) (!phase)) source next appended used pad (processed + 2) count).tapeCells ≤ space := by
      simp only [config_cells]
      dsimp only [space]
      rw [happ]
      have hn : 2 * (used + pad) ≤ (rows.length + 3) * (used + pad) := Nat.mul_le_mul_right _ (by omega)
      omega
    have hreturn : step machine
        (controlConfig (UnaryController.code (s := 22) phase)
          (config (21 : Fin 22) source next appended used pad (processed + 2) count)) =
        some (config (UnaryController.test (s := 22) (!phase)) source next appended used pad (processed + 2) count) := by
      have h := UnaryController.return_step family phase body.final (processed + 2) driver halted
      rw [hbf] at h
      exact h
    have hbodyEnd : (controlConfig (UnaryController.code (s := 22) phase)
        (config (21 : Fin 22) source next appended used pad (processed + 2) count)).tapeCells ≤ space := hend
    have returned := Prefix.step hbodyEnd (UnaryController.body_halted _ _ _) hreturn tailPrefix'
    let core := PaddedRow.config PaddedRow.machine.start source pre.length out used pad
    have hread := UnaryTemplate.tape_mark count processed (by simp only [List.length_cons] at hcount; omega)
    have henter : step machine
        (config (UnaryController.test (s := 22) phase) source pre.length out used pad (processed + 1) count) =
        some (controlConfig (UnaryController.code (s := 22) phase)
          (config PaddedRow.machine.start source pre.length out used pad (processed + 2) count)) :=
      UnaryController.enter_step family phase core.heads core.tapes (processed + 1) driver hread
    have hstart : (config (UnaryController.test (s := 22) phase) source pre.length out used pad (processed + 1) count).tapeCells ≤ space := by
      simp only [config_cells]
      dsimp only [space]
      have hn : used + pad ≤ (rows.length + 3) * (used + pad) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have joined := Prefix.step hstart (UnaryController.test_halted _ _) henter (bp'.trans returned)
    have htime : body.steps + ((fields rows).length + rows.length * (3 * used + 2 * pad + 11) + 1 + 1) + 1 =
        (fields (row :: rows)).length + (row :: rows).length * (3 * used + 2 * pad + 11) + 1 := by
      rw [hbs, hfields, List.length_cons, Nat.add_mul]
      omega
    rw [htime] at joined
    exact ⟨finalPhase, joined⟩

theorem matrix_run (pre : List Bool) (rows : List (List Record)) (suffix out : List Bool)
    (used pad : ℕ) (hw : ∀ row ∈ rows, row.length = used) :
    ∃ finalPhase, ∃ r : ExecutionReceipt 5 48,
      runFrom machine ((fields rows).length + rows.length * (3 * used + 2 * pad + 11) + 1)
        (config machine.start (pre ++ fields rows ++ suffix) pre.length out used pad 1 rows.length) = some r ∧
      r.final = config (UnaryController.stop (s := 22) finalPhase) (pre ++ fields rows ++ suffix)
        (pre.length + (fields rows).length) (out ++ output pad rows) used pad (rows.length + 1) rows.length ∧
      r.steps = (fields rows).length + rows.length * (3 * used + 2 * pad + 11) + 1 ∧
      r.peakTapeCells ≤ (pre ++ fields rows ++ suffix).length + out.length + (rows.length + 2) * (used + pad) + rows.length + 6 := by
  obtain ⟨phase, hp⟩ := loop_prefix false pre rows suffix out used pad 0 rows.length hw (by simp)
  have hout := output_length pad used rows hw
  obtain ⟨r, hr, hf, hs, hb⟩ := hp.run (UnaryController.stop_halted family phase) (by
    simp only [config_cells, List.length_append, hout, Nat.add_mul]
    omega)
  exact ⟨phase, r, hr, hf, hs, hb⟩

end NearCubicWires.RepairOrdinary.MatrixRows
