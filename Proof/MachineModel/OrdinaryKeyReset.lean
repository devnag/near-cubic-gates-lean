import Proof.MachineModel.OrdinarySelectiveWorkspace

/-! A repeatable keyed bucket scan. The actual source cursor is returned to0;
the aggregate output endpoint and all bounded keyed workspace are preserved. -/
namespace NearCubicWires.RepairOrdinary.KeyReset
open LocalBitMultitape KeyCell
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 21 57 := SelectiveReset.machine KeyLoop.machine 15
def config {s : ℕ} (state : Fin s) (W a b rank : ℕ) (upper record clone : List Bool)
    (mask : Bool) (source out : List Bool) (K I inner keyCap resetCap : ℕ) : Configuration 21 s :=
  TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => List.replicate resetCap false)
    (KeyCell.config state W a b rank upper record clone mask source 0 out K I inner keyCap)

theorem padded_initial (W a b rank : ℕ) (upper record clone : List Bool)
    (mask : Bool) (source out : List Bool) (K I inner keyCap resetCap : ℕ) :
    ZeroPadding.config (Rewind.Workspace.capacities 20 resetCap)
      (Rewind.recording (KeyCell.config (RecordController.test 53) W a b rank upper record clone mask source 0 out K I inner keyCap) 0) =
      config machine.start W a b rank upper record clone mask source out K I inner keyCap resetCap := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [ZeroPadding.config, Rewind.Workspace.capacities, Rewind.recording, Rewind.config,
        config, TapeEmbedding.config, ZeroPadding.pad]
    all_goals rfl

theorem reset_final (W a b rank : ℕ) (upper record clone : List Bool)
    (mask : Bool) (source : List Bool) (pos : ℕ) (out : List Bool) (K I inner keyCap resetCap : ℕ) :
    let core := KeyCell.config (RecordController.stop 53) W a b rank upper record clone mask source pos out K I inner keyCap
    SelectiveReset.finished (s := 55) (fun i => if i = (15 : Fin 20) then 0 else core.heads i) core.tapes resetCap =
      config 56 W a b rank upper record clone mask source out K I inner keyCap resetCap := by
  dsimp only
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · fin_cases j <;> simp [SelectiveReset.finished, Rewind.config, config, TapeEmbedding.config,
        KeyCell.config, RecordCell.config, CellEmit.config, RecordCell.recordHeads, Fin.addCases]
    · simp [SelectiveReset.finished, Rewind.config, config, TapeEmbedding.config]
  · rfl

theorem scan_run (S K I inner keyCap resetCap a b initialRank : ℕ) (records : List KeyLoop.Record)
    (upper recordBack cloneBack out : List Bool) (mask : Bool)
    (hfit : a + b < 2 ^ (K + S + 1)) (hrecords : ∀ r ∈ records, r.2.2 < 2 ^ (K + S + 1))
    (hu : upper.length ≤ 2 * (K + S + 1) + 1) (hr : recordBack.length ≤ 4 * (K + S + 1) + 1)
    (hc : cloneBack.length ≤ 4 * (K + S + 1) + 1) (hci : 2 * I ≤ keyCap) (hck : 2 * K ≤ keyCap)
    (hreset : records.length * (68 * (K + S + 1) + 4 * (I + K) + 63) + 1 ≤ resetCap) :
    let W := K + S + 1
    let fuel := records.length * (68 * W + 4 * (I + K) + 63) + 1
    ∃ finalRank finalUpper finalRecord finalClone,
      finalUpper.length ≤ 2 * W + 1 ∧ finalRecord.length ≤ 4 * W + 1 ∧ finalClone.length ≤ 4 * W + 1 ∧
      ∃ r : ExecutionReceipt 21 57,
        runFrom machine (2 * fuel + 2)
          (config machine.start W a b initialRank upper recordBack cloneBack mask (KeyLoop.stream S K records) out
            K I inner keyCap resetCap) = some r ∧
        r.final = config 56 W a b finalRank finalUpper finalRecord finalClone mask (KeyLoop.stream S K records)
          (out ++ KeyLoop.output K I inner a b mask records) K I inner keyCap resetCap ∧
        r.steps ≤ 2 * fuel + 2 ∧
        r.peakTapeCells ≤ (KeyLoop.stream S K records).length + 104 * W + 8 * I + 6 * K + out.length +
          records.length * (2 * (I + K) + 3) + keyCap + 64 + fuel + resetCap := by
  dsimp only
  let W := K + S + 1
  let fuel := records.length * (68 * W + 4 * (I + K) + 63) + 1
  obtain ⟨finalRank, finalUpper, finalRecord, finalClone, hfu, hfr, hfc, body, hbody, hbf, hbs, hbp⟩ :=
    KeyLoop.loop_run S K I inner keyCap a b initialRank records [] upper recordBack cloneBack out mask hfit hrecords hu hr hc hci hck
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at hbody hbf hbp
  obtain ⟨r, hr, hf, hs, hp⟩ := SelectiveReset.workspace_run KeyLoop.machine (15 : Fin 20) fuel resetCap _ body hbody (by rfl) (hbs.trans hreset)
  rw [padded_initial] at hr
  rw [hbf, reset_final] at hf
  have hbound : 2 * body.steps + 2 ≤ 2 * fuel + 2 := by dsimp only [fuel, W]; omega
  have hmore := runFrom_moreFuel machine (2 * body.steps + 2) ((2 * fuel + 2) - (2 * body.steps + 2)) _ r hr
  rw [Nat.add_sub_of_le hbound] at hmore
  dsimp only [fuel, W] at hbound
  exact ⟨finalRank, finalUpper, finalRecord, finalClone, hfu, hfr, hfc, r, hmore, hf, by omega, by omega⟩

end NearCubicWires.RepairOrdinary.KeyReset
