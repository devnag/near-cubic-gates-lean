import Proof.MachineModel.OrdinaryRecordLoad

/-! The actual annotated-record cell body. Rank extraction and the scalar
cell emitter share a physical rank tape; no intermediate rank stream is
materialized. Original occurrence records remain available for coordinates. -/
namespace NearCubicWires.RepairOrdinary.RecordCell
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def layout : Fin 16 ≃ Fin 16 where
  toFun := ![9, 10, 11, 12, 4, 13, 14, 15, 0, 1, 2, 3, 5, 6, 7, 8]
  invFun := ![8, 9, 10, 11, 4, 12, 13, 14, 15, 0, 1, 2, 3, 5, 6, 7]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem layout_inverse : (layout.symm : Fin 16 → Fin 16) = ![8, 9, 10, 11, 4, 12, 13, 14, 15, 0, 1, 2, 3, 5, 6, 7] := rfl
def load : Machine 16 21 := TapeRenaming.machine layout (TapeEmbedding.machine 8 RecordLoad.machine)
def emit : Machine 16 20 := TapeEmbedding.machine 7 CellEmit.machine
def machine : Machine 16 41 := Composition.machine load emit
def recordTapes (width : ℕ) (recordBacking cloneBacking source : List Bool) : Fin 7 → List Bool :=
  ![recordBacking, cloneBacking, List.replicate (4 * width + 1) false, List.replicate (8 * width + 3) false,
    List.replicate (2 * width + 1) false, List.replicate (24 * width + 14) false, source]
def recordHeads (position : ℕ) : Fin 7 → ℕ := ![0, 0, 0, 0, 0, 0, position]
def config {s : ℕ} (state : Fin s) (width a b rank : ℕ) (upperBacking recordBacking cloneBacking : List Bool)
    (mask : Bool) (source : List Bool) (position : ℕ) (out : List Bool) : Configuration 16 s :=
  TapeEmbedding.config (recordHeads position) (recordTapes width recordBacking cloneBacking source)
    (CellEmit.config state (LocalCell.input width a b rank upperBacking mask) out)

def cellHeads (out : List Bool) : Fin 8 → ℕ := ![0, 0, 0, 0, 0, 0, 0, out.length]
def cellTapes (width a b : ℕ) (upperBacking : List Bool) (mask : Bool) (out : List Bool) : Fin 8 → List Bool :=
  ![frame (binary width a), frame (binary width b), upperBacking, List.replicate (2 * width + 1) false,
    [false], [mask], List.replicate (6 * width + 6) false, out]

theorem place_initial {s : ℕ} (state : Fin s) (word : List Bool) (rank oldRank a b : ℕ)
    (upperBacking recordBacking cloneBacking : List Bool) (mask : Bool) (source : List Bool) (pos : ℕ) (out : List Bool) :
    TapeRenaming.config layout (TapeEmbedding.config (cellHeads out) (cellTapes word.length a b upperBacking mask out)
      (RecordLoad.config state (RecordLoad.workspace word (binary word.length rank) recordBacking cloneBacking
        (frame (binary word.length oldRank))) source pos)) =
      config state word.length a b oldRank upperBacking recordBacking cloneBacking mask source pos out := by
  have h4 : 2 * (word.length + word.length) + 1 = 4 * word.length + 1 := by omega
  have h8 : 4 * (word.length + word.length) + 3 = 8 * word.length + 3 := by omega
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, RecordLoad.config, config,
      CellEmit.config, recordHeads, cellHeads, Fin.addCases]
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, RecordLoad.config, config,
      CellEmit.config, LocalCell.input, LocalCell.raw, recordTapes, cellTapes, RecordLoad.workspace,
      RecordExtractReset.input, RecordExtract.input, RecordClone.input, RecordClone.raw, Fin.addCases, h4, h8]

theorem place_loaded {s : ℕ} (state : Fin s) (word : List Bool) (rank a b : ℕ)
    (upperBacking : List Bool) (mask : Bool) (source : List Bool) (pos : ℕ) (out : List Bool) :
    TapeRenaming.config layout (TapeEmbedding.config (cellHeads out) (cellTapes word.length a b upperBacking mask out)
      (RecordLoad.config state (RecordExtractReset.output word (binary word.length rank)) source pos)) =
      config state word.length a b rank upperBacking (frame (word ++ binary word.length rank))
        (frame (word ++ binary word.length rank)) mask source pos out := by
  have h4 : 2 * (word.length + word.length) + 1 = 4 * word.length + 1 := by omega
  have h8 : 4 * (word.length + word.length) + 3 = 8 * word.length + 3 := by omega
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, RecordLoad.config, config,
      CellEmit.config, recordHeads, cellHeads, Fin.addCases]
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, RecordLoad.config, config,
      CellEmit.config, LocalCell.input, LocalCell.raw, recordTapes, cellTapes,
      RecordExtractReset.output, RecordExtract.finished, Fin.addCases, h4, h8]

theorem emit_output (width a b rank : ℕ) (mask : Bool) :
    CellEmit.cleared (LocalCell.output width a b rank mask) =
      LocalCell.input width a b rank (frame (binary width (a + b))) mask := by
  funext i
  fin_cases i <;> simp [CellEmit.cleared, LocalCell.output, LocalCell.input, LocalCell.raw, Fin.addCases]

end NearCubicWires.RepairOrdinary.RecordCell

