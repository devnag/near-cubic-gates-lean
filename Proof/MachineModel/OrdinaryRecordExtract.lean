import Proof.MachineModel.OrdinaryRecordHalf

/-! Extract the framed rank from an actual annotated record, including local
copying and midpoint discovery. The original record and both counters are
retained explicitly for the enclosing cursor-preserving record scan. -/
namespace NearCubicWires.RepairOrdinary.RecordExtract
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def layout : Fin 6 ≃ Fin 6 where
  toFun := ![1, 4, 5, 0, 2, 3]
  invFun := ![3, 0, 4, 5, 1, 2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem layout_inverse : (layout.symm : Fin 6 → Fin 6) = ![3, 0, 4, 5, 1, 2] := rfl
def prepare : Machine 6 11 := TapeEmbedding.machine 2 RecordHalf.machine
def extract : Machine 6 4 := TapeRenaming.machine layout (TapeEmbedding.machine 3 FrameLoad.machine)
def machine : Machine 6 15 := Composition.machine prepare extract
def input (word rank backing rankBacking : List Bool) : Fin 6 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (4 + 2) => List Bool) (RecordClone.input (word ++ rank) backing)
    ![rankBacking, List.replicate (2 * word.length + 1) false]
def finished (word rank : List Bool) : Configuration 6 15 :=
  ⟨14, ![4 * word.length, 4 * word.length + 1, 0, 0, 0, 0],
    ![frame (word ++ rank), frame (word ++ rank), List.replicate (2 * (word ++ rank).length + 1) false,
      List.replicate (4 * (word ++ rank).length + 3) false, frame rank,
      List.replicate (2 * word.length + 1) false]⟩

theorem extract_run (word rank backing rankBacking : List Bool) (hw : rank.length = word.length)
    (hb : backing.length ≤ 4 * word.length + 1) (hrb : rankBacking.length ≤ 2 * word.length + 1) :
    ∃ r : ExecutionReceipt 6 15,
      run machine (24 * word.length + 14) (input word rank backing rankBacking) = some r ∧
      r.final = finished word rank ∧ r.steps = 24 * word.length + 14 ∧
      r.peakTapeCells ≤ 40 * word.length + 13 := by
  obtain ⟨half, hhalf, hhf, hhs, hhp⟩ := RecordHalf.half_run word rank backing hw hb
  let extras : Fin 2 → List Bool := ![rankBacking, List.replicate (2 * word.length + 1) false]
  have he := TapeEmbedding.run_embed RecordHalf.machine (fun _ : Fin 2 => 0) extras _ _ half hhalf
  let first := TapeEmbedding.receipt (fun _ : Fin 2 => 0) extras half
  obtain ⟨field, hfield, hff, hfs, hfp⟩ := CellLoad.loader_run (Streaming.marks word) rank [] rankBacking (by simpa [hw] using hrb)
  have hsource : Streaming.marks word ++ frame rank ++ [] = frame (word ++ rank) := by
    simp [Streaming.frame_append]
  simp only [hsource, Streaming.marks_length, hw] at hfield hff hfs hfp
  let otherHeads : Fin 3 → ℕ := ![4 * word.length, 0, 0]
  let otherTapes : Fin 3 → List Bool := ![frame (word ++ rank), List.replicate (2 * (word ++ rank).length + 1) false,
    List.replicate (4 * (word ++ rank).length + 3) false]
  have hfe := TapeEmbedding.run_embed FrameLoad.machine otherHeads otherTapes _ _ field hfield
  have hq := TapeRenaming.run_rename layout (TapeEmbedding.machine 3 FrameLoad.machine) _ _ _ hfe
  let second := TapeRenaming.receipt layout (TapeEmbedding.receipt otherHeads otherTapes field)
  have hmid : Composition.restart first.final extract.start =
      TapeRenaming.config layout (TapeEmbedding.config otherHeads otherTapes
        (CellLoad.loaderInput (frame (word ++ rank)) (2 * word.length) rankBacking word.length)) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.restart, first, TapeEmbedding.receipt, TapeEmbedding.config,
        hhf, RecordHalf.finished, TapeRenaming.config, CellLoad.loaderInput, otherHeads, Fin.addCases]
    · funext i
      fin_cases i <;> simp [Composition.restart, first, TapeEmbedding.receipt, TapeEmbedding.config,
        hhf, RecordHalf.finished, RecordClone.output, TapeRenaming.config, CellLoad.loaderInput,
        extras, otherTapes, Fin.addCases]
  have hq' : runFrom extract (4 * word.length + 3) (Composition.restart first.final extract.start) = some second := by
    rw [hmid]
    exact hq
  have hj := Composition.run_join prepare extract (20 * word.length + 10) (4 * word.length + 3)
    (TapeEmbedding.config (fun _ : Fin 2 => 0) extras
      (initialConfiguration RecordHalf.machine (RecordClone.input (word ++ rank) backing))) first second he hq'
  have hi : Composition.leftConfig 4 (TapeEmbedding.config (fun _ : Fin 2 => 0) extras
      (initialConfiguration RecordHalf.machine (RecordClone.input (word ++ rank) backing))) =
      initialConfiguration machine (input word rank backing rankBacking) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.leftConfig, TapeEmbedding.config, initialConfiguration, Fin.addCases]
    · rfl
  have htime : (20 * word.length + 10) + 1 + (4 * word.length + 3) = 24 * word.length + 14 := by omega
  refine ⟨Composition.joinedReceipt first second, by rw [hi, htime] at hj; exact hj, ?_, ?_, ?_⟩
  · apply configuration_ext
    · change field.final.control.natAdd 11 = (14 : Fin 15)
      rw [hff]
      change (3 : Fin 4).natAdd 11 = (14 : Fin 15)
      decide
    · funext i
      fin_cases i <;> simp [Composition.joinedReceipt, Composition.rightConfig, second,
        TapeRenaming.receipt, TapeRenaming.config, TapeEmbedding.receipt, TapeEmbedding.config,
        hff, FrameLoad.reset, finished, otherHeads, Fin.addCases]
      omega
    · funext i
      fin_cases i <;> simp [Composition.joinedReceipt, Composition.rightConfig, second,
        TapeRenaming.receipt, TapeRenaming.config, TapeEmbedding.receipt, TapeEmbedding.config,
        hff, FrameLoad.reset, finished, otherTapes, Fin.addCases]
  · change half.steps + 1 + field.steps = _
    omega
  · change max (half.peakTapeCells + TapeEmbedding.extraCells extras)
      (field.peakTapeCells + TapeEmbedding.extraCells otherTapes) ≤ _
    simp [TapeEmbedding.extraCells, extras, otherTapes, Fin.sum_univ_succ, hw]
    simp only [frame_length, List.length_append, hw] at hfp
    omega

end NearCubicWires.RepairOrdinary.RecordExtract
