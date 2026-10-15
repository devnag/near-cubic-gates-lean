import Proof.MachineModel.OrdinaryKeyPair

/-! Fixed physical layout for a keyed left cell. Original annotated records,
source/output cursors and both coordinate templates are retained. -/
namespace NearCubicWires.RepairOrdinary.KeyCell
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extraTapes (K I inner cap : ℕ) : Fin 4 → List Bool :=
  ![frame (binary K 0), frame (binary I inner), frame (binary I 0), List.replicate cap false]
def config {s : ℕ} (state : Fin s) (W a b rank : ℕ) (upper record clone : List Bool)
    (mask : Bool) (source : List Bool) (pos : ℕ) (out : List Bool) (K I inner cap : ℕ) : Configuration 20 s :=
  TapeEmbedding.config (fun _ : Fin 4 => 0) (extraTapes K I inner cap)
    (RecordCell.config state W a b rank upper record clone mask source pos out)

def layout : Fin 20 ≃ Fin 20 where
  toFun := ![17, 18, 9, 16, 8, 19, 0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15]
  invFun := ![6, 7, 8, 9, 10, 11, 12, 13, 4, 2, 14, 15, 16, 17, 18, 19, 3, 0, 1, 5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem layout_inverse : (layout.symm : Fin 20 → Fin 20) =
    ![6, 7, 8, 9, 10, 11, 12, 13, 4, 2, 14, 15, 16, 17, 18, 19, 3, 0, 1, 5] := rfl

def keyHeads (pos : ℕ) : Fin 14 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, pos]
def keyTapes (W a b rank : ℕ) (upper clone : List Bool) (mask : Bool) (source : List Bool) : Fin 14 → List Bool :=
  ![frame (binary W a), frame (binary W b), upper, List.replicate (2 * W + 1) false,
    frame (binary W rank), [false], [mask], List.replicate (6 * W + 6) false,
    clone, List.replicate (4 * W + 1) false, List.replicate (8 * W + 3) false,
    List.replicate (2 * W + 1) false, List.replicate (24 * W + 14) false, source]

def cell : Machine 20 41 := TapeEmbedding.machine 4 RecordCell.machine
def key : Machine 20 10 := TapeRenaming.machine layout (TapeEmbedding.machine 14 KeyPair.machine)
def mark : Machine 20 2 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 1
  rule := fun state _ => if state.val = 0 then
    some ⟨1, fun i => if i.val = 8 then some true else none,
      fun i => if i.val = 8 then .right else .stay⟩ else none
def tail : Machine 20 51 := Composition.machine cell key
def machine : Machine 20 53 := Composition.machine mark tail

theorem place_key {s : ℕ} (state : Fin s) (W a b rank : ℕ) (upper record clone : List Bool)
    (mask : Bool) (source : List Bool) (pos : ℕ) (out : List Bool) (K I inner cap : ℕ) :
    TapeRenaming.config layout (TapeEmbedding.config (keyHeads pos) (keyTapes W a b rank upper clone mask source)
      (KeyPair.config state (frame (binary I inner)) (frame (binary I 0)) record (frame (binary K 0)) out cap)) =
      config state W a b rank upper record clone mask source pos out K I inner cap := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, KeyPair.config, config,
      RecordCell.config, CellEmit.config, RecordCell.recordHeads, keyHeads, Fin.addCases]
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, KeyPair.config, config,
      RecordCell.config, CellEmit.config, LocalCell.input, LocalCell.raw, RecordCell.recordTapes,
      extraTapes, keyTapes, Fin.addCases]

@[simp] theorem key_cells (W a b rank : ℕ) (upper clone : List Bool) (mask : Bool) (source : List Bool) :
    TapeEmbedding.extraCells (keyTapes W a b rank upper clone mask source) =
      52 * W + 31 + upper.length + clone.length + source.length := by
  simp [TapeEmbedding.extraCells, keyTapes, Fin.sum_univ_succ]
  omega

@[simp] theorem extra_cells (K I inner cap : ℕ) :
    TapeEmbedding.extraCells (extraTapes K I inner cap) = 2 * K + 4 * I + cap + 3 := by
  simp [TapeEmbedding.extraCells, extraTapes, Fin.sum_univ_succ]
  omega

@[simp] theorem config_cells {s : ℕ} (state : Fin s) (W a b rank : ℕ) (upper record clone : List Bool)
    (mask : Bool) (source : List Bool) (pos : ℕ) (out : List Bool) (K I inner cap : ℕ) :
    (config state W a b rank upper record clone mask source pos out K I inner cap).tapeCells =
      source.length + out.length + upper.length + record.length + clone.length + 52 * W + 2 * K + 4 * I + cap + 34 := by
  simp [config, TapeEmbedding.config_cells, RecordLoop.config_cells]
  omega

theorem mark_run (W a b rank : ℕ) (upper record clone : List Bool)
    (mask : Bool) (source : List Bool) (pos : ℕ) (out : List Bool) (K I inner cap : ℕ) :
    RankBody.Executes mark 1
      (source.length + out.length + upper.length + record.length + clone.length + 52 * W + 2 * K + 4 * I + cap + 35)
      (config 0 W a b rank upper record clone mask source pos out K I inner cap)
      (config 1 W a b rank upper record clone mask source pos (out ++ [true]) K I inner cap) := by
  have he : step mark (config 0 W a b rank upper record clone mask source pos out K I inner cap) =
      some (config 1 W a b rank upper record clone mask source pos (out ++ [true]) K I inner cap) := by
    simp [step, mark, config, TapeEmbedding.config, RecordCell.config, CellEmit.config]
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [applyAction, HeadMove.apply, RecordCell.recordHeads, Fin.addCases]
    · funext i
      fin_cases i <;> simp [applyAction, Fin.addCases, Streaming.write_append]
  have hp := Prefix.step (by simp :
      (config 0 W a b rank upper record clone mask source pos out K I inner cap).tapeCells ≤
      source.length + out.length + upper.length + record.length + clone.length + 52 * W + 2 * K + 4 * I + cap + 35)
    (by rfl : mark.halted (0 : Fin 2) = false) he (Prefix.refl _ (by simp; omega))
  obtain ⟨r, hr, hf, hs, hb⟩ := hp.run (by rfl) (by simp; omega)
  exact ⟨r, hr, hf, hs.le, hb⟩

end NearCubicWires.RepairOrdinary.KeyCell
