import Proof.MachineModel.OrdinaryMemoryScan
import Proof.MachineModel.OrdinaryRecordLoad
import Proof.MachineModel.OrdinaryCompare

/-! Actual advancing-stream record loading and cell equality for the memory
checker. Equal field widths reuse the existing loader. Since the stream is
sorted, current <= previous is exactly cell equality. The old value remains
on its own tape for the following fixed Boolean acceptance step. -/
namespace NearCubicWires.RepairOrdinary.MemoryCompare
open LocalBitMultitape MemoryLog MemorySort StablePartition SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def front (I timestamp : ℕ) (e : Event) : List Bool :=
  e.read :: e.after :: binary I timestamp
def key (I W : ℕ) (e : Event) : List Bool := binary (I+2) (cellCode W e.cell)

@[simp] theorem front_length (I timestamp : ℕ) (e : Event) :
    (front I timestamp e).length = I+2 := by simp [front]
@[simp] theorem key_length (I W : ℕ) (e : Event) : (key I W e).length = I+2 := by simp [key]
theorem record_frame (I W timestamp : ℕ) (e : Event) :
    recordBits (encoded I (I+2) W timestamp e) = frame (front I timestamp e ++ key I W e) := by
  simp [recordBits, encoded, front, key, frame]

def layout : Fin 11 ≃ Fin 11 where
  toFun := ![4, 8, 10, 0, 1, 2, 3, 5, 6, 7, 9]
  invFun := ![3, 4, 5, 6, 0, 7, 8, 9, 1, 10, 2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem layout_inverse : (layout.symm : Fin 11 → Fin 11) =
    ![3, 4, 5, 6, 0, 7, 8, 9, 1, 10, 2] := rfl
def load : Machine 11 21 := TapeEmbedding.machine 3 RecordLoad.machine
def compare : Machine 11 5 := TapeRenaming.machine layout (TapeEmbedding.machine 8 Compare.machine)
def machine : Machine 11 26 := Composition.machine load compare

def config {s : ℕ} (state : Fin s) (workspace : Fin 7 → List Bool)
    (source : List Bool) (position : ℕ) (previousKey : List Bool) (previousAfter : Bool)
    (out : List Bool) : Configuration 11 s :=
  TapeEmbedding.config ![0, 0, out.length] ![frame previousKey, [previousAfter], out]
    (RecordLoad.config state workspace source position)

def finished {s : ℕ} (state : Fin s) (K : ℕ) (workspace : Fin 7 → List Bool)
    (source : List Bool) (position : ℕ) (previousKey : List Bool) (previousAfter : Bool)
    (out : List Bool) : Configuration 11 s :=
  ⟨state, ![0, 0, 0, 0, 2*K, 0, 0, position, 2*K, 0, out.length],
    ![workspace 0, workspace 1, workspace 2, workspace 3, workspace 4, workspace 5, workspace 6,
      source, frame previousKey, [previousAfter], out]⟩

theorem equality_bit (I W : ℕ) (previous current : Event)
    (hp : cellCode W previous.cell < 2^(I+2))
    (hc : cellCode W current.cell < 2^(I+2))
    (hap : previous.cell.2 < 2^W) (hac : current.cell.2 < 2^W)
    (order : cellCode W previous.cell ≤ cellCode W current.cell) :
    decide (RadixSemantics.value (key I W current) ≤ RadixSemantics.value (key I W previous)) =
      decide (current.cell = previous.cell) := by
  rw [key, key, binary_value _ _ hc, binary_value _ _ hp]
  rw [decide_eq_decide]
  constructor
  · intro h
    exact MemoryScan.cellCode_injective W current.cell previous.cell hac hap (Nat.le_antisymm h order)
  · intro h
    rw [h]

theorem load_compare_run (I W timestamp : ℕ) (previous current : Event)
    (pre suffix recordBacking cloneBacking rankBacking out : List Bool)
    (hrecord : recordBacking.length ≤ 4*(I+2)+1)
    (hclone : cloneBacking.length ≤ 4*(I+2)+1)
    (hrank : rankBacking.length ≤ 2*(I+2)+1)
    (hp : cellCode W previous.cell < 2^(I+2))
    (hc : cellCode W current.cell < 2^(I+2))
    (hap : previous.cell.2 < 2^W) (hac : current.cell.2 < 2^W)
    (order : cellCode W previous.cell ≤ cellCode W current.cell) :
    ∃ r : ExecutionReceipt 11 26,
      runFrom machine (58*(I+2)+36)
        (config machine.start
          (RecordLoad.workspace (front I timestamp current) (key I W current)
            recordBacking cloneBacking rankBacking)
          (pre ++ recordBits (encoded I (I+2) W timestamp current) ++ suffix) pre.length
          (key I W previous) previous.after out) = some r ∧
      r.final = finished 25 (I+2)
        (RecordExtractReset.output (front I timestamp current) (key I W current))
        (pre ++ recordBits (encoded I (I+2) W timestamp current) ++ suffix)
        (pre.length+4*(I+2)+1) (key I W previous) previous.after
        (out ++ [decide (current.cell = previous.cell)]) ∧
      r.steps = 58*(I+2)+36 := by
  let word := front I timestamp current
  let rank := key I W current
  let source := pre ++ recordBits (encoded I (I+2) W timestamp current) ++ suffix
  let next := pre.length+4*(I+2)+1
  let workspace := RecordExtractReset.output word rank
  obtain ⟨loaded, hl, hlf, hls, _⟩ := RecordLoad.load_run word rank pre suffix
    recordBacking cloneBacking rankBacking (by simp [word, rank])
    (by simpa [word] using hrecord) (by simpa [word] using hclone) (by simpa [word] using hrank)
  have hsource : pre ++ frame (word ++ rank) ++ suffix = source := by
    dsimp only [source, word, rank]
    rw [record_frame]
  have hword : word.length = I+2 := front_length I timestamp current
  rw [hsource] at hl hlf
  rw [hword] at hl hlf hls
  let extraHeads : Fin 3 → ℕ := ![0, 0, out.length]
  let extraTapes : Fin 3 → List Bool := ![frame (key I W previous), [previous.after], out]
  have hlift := TapeEmbedding.run_embed RecordLoad.machine extraHeads extraTapes _ _ loaded hl
  let first := TapeEmbedding.receipt extraHeads extraTapes loaded
  obtain ⟨compared, hq, hqf, hqs, _⟩ := Compare.compare_run [] [] rank (key I W previous) [] [] out
    (by simp [rank])
  have heq := equality_bit I W previous current hp hc hap hac order
  simp only [List.nil_append, List.append_nil, List.length_nil, zero_add,
    key_length, rank] at hq hqf hqs
  rw [heq] at hqf
  let otherHeads : Fin 8 → ℕ := ![0, 0, 0, 0, 0, 0, next, 0]
  let otherTapes : Fin 8 → List Bool :=
    ![workspace 0, workspace 1, workspace 2, workspace 3, workspace 5, workspace 6, source, [previous.after]]
  have hqe := TapeEmbedding.run_embed Compare.machine otherHeads otherTapes _ _ compared hq
  have hqr := TapeRenaming.run_rename layout (TapeEmbedding.machine 8 Compare.machine) _ _ _ hqe
  let second := TapeRenaming.receipt layout (TapeEmbedding.receipt otherHeads otherTapes compared)
  have hmid : Composition.restart first.final compare.start =
      TapeRenaming.config layout (TapeEmbedding.config otherHeads otherTapes
        (Compare.config (Compare.scanState true) (frame (key I W current))
          (frame (key I W previous)) 0 0 out)) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.restart, first, TapeEmbedding.receipt, TapeEmbedding.config,
        hlf, RecordLoad.config, TapeRenaming.config, Compare.config,
        extraHeads, otherHeads, next, Fin.addCases]
    · funext i
      fin_cases i <;> simp [Composition.restart, first, TapeEmbedding.receipt, TapeEmbedding.config,
        hlf, RecordLoad.config, TapeRenaming.config, Compare.config,
        extraTapes, otherTapes, workspace, RecordExtractReset.output, RecordExtract.finished, rank, Fin.addCases]
  have hqr' : runFrom compare (2*(I+2)+1) (Composition.restart first.final compare.start) = some second := by
    rw [hmid]
    exact hqr
  have hj := Composition.run_join load compare (56*(I+2)+34) (2*(I+2)+1)
    (TapeEmbedding.config extraHeads extraTapes
      (RecordLoad.config RecordLoad.machine.start
        (RecordLoad.workspace word rank recordBacking cloneBacking rankBacking) source pre.length))
      first second hlift hqr'
  have htime : (56*(I+2)+34)+1+(2*(I+2)+1) = 58*(I+2)+36 := by omega
  refine ⟨Composition.joinedReceipt first second, ?_, ?_, ?_⟩
  · rw [htime] at hj
    exact hj
  · apply configuration_ext
    · change compared.final.control.natAdd 21 = (25 : Fin 26)
      rw [hqf]
      rfl
    · funext i
      fin_cases i <;> simp [Composition.joinedReceipt, Composition.rightConfig, second,
        TapeRenaming.receipt, TapeRenaming.config, TapeEmbedding.receipt, TapeEmbedding.config,
        hqf, Compare.config, finished, otherHeads, next, Fin.addCases]
    · funext i
      fin_cases i <;> simp [Composition.joinedReceipt, Composition.rightConfig, second,
        TapeRenaming.receipt, TapeRenaming.config, TapeEmbedding.receipt, TapeEmbedding.config,
        hqf, Compare.config, finished, otherTapes, workspace, RecordExtractReset.output,
        RecordExtract.finished, word, rank, source, Fin.addCases]
  · change loaded.steps+1+compared.steps = _
    omega

end NearCubicWires.RepairOrdinary.MemoryCompare
