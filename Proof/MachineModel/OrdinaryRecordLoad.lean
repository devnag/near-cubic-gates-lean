import Proof.MachineModel.OrdinaryRecordExtractReset

/-! Read one actual annotated record from the advancing table cursor, extract
its framed rank and reset only bounded local work tapes. -/
namespace NearCubicWires.RepairOrdinary.RecordLoad
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def layout : Fin 8 ≃ Fin 8 where
  toFun := ![7, 0, 2, 1, 3, 4, 5, 6]
  invFun := ![1, 3, 2, 4, 5, 6, 7, 0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem layout_inverse : (layout.symm : Fin 8 → Fin 8) = ![1, 3, 2, 4, 5, 6, 7, 0] := rfl
def load : Machine 8 4 := TapeRenaming.machine layout (TapeEmbedding.machine 5 FrameLoad.machine)
def extract : Machine 8 17 := TapeEmbedding.machine 1 RecordExtractReset.machine
def machine : Machine 8 21 := Composition.machine load extract
def config {s : ℕ} (state : Fin s) (tapes : Fin 7 → List Bool) (source : List Bool) (position : ℕ) : Configuration 8 s :=
  TapeEmbedding.config (fun _ : Fin 1 => position) (fun _ => source) ⟨state, fun _ => 0, tapes⟩
def workspace (word rank recordBacking cloneBacking rankBacking : List Bool) : Fin 7 → List Bool :=
  Function.update (RecordExtractReset.input word rank cloneBacking rankBacking) 0 recordBacking

theorem load_run (word rank pre suffix recordBacking cloneBacking rankBacking : List Bool)
    (hw : rank.length = word.length) (hrecord : recordBacking.length ≤ 4 * word.length + 1)
    (hclone : cloneBacking.length ≤ 4 * word.length + 1) (hrank : rankBacking.length ≤ 2 * word.length + 1) :
    ∃ r : ExecutionReceipt 8 21,
      runFrom machine (56 * word.length + 34)
        (config machine.start (workspace word rank recordBacking cloneBacking rankBacking)
          (pre ++ frame (word ++ rank) ++ suffix) pre.length) = some r ∧
      r.final = config 20 (RecordExtractReset.output word rank) (pre ++ frame (word ++ rank) ++ suffix)
        (pre.length + 4 * word.length + 1) ∧
      r.steps = 56 * word.length + 34 ∧
      r.peakTapeCells ≤ (pre ++ frame (word ++ rank) ++ suffix).length + 88 * word.length + 41 := by
  let source := pre ++ frame (word ++ rank) ++ suffix
  let next := pre.length + 4 * word.length + 1
  have hlen : (word ++ rank).length = 2 * word.length := by simp [hw]; omega
  obtain ⟨base, hr, hf, hs, hp⟩ := CellLoad.loader_run pre (word ++ rank) suffix recordBacking (by simp [hw]; omega)
  let extras : Fin 5 → List Bool := ![cloneBacking, List.replicate (4 * (word ++ rank).length + 3) false,
    rankBacking, List.replicate (2 * word.length + 1) false, List.replicate (24 * word.length + 14) false]
  have he := TapeEmbedding.run_embed FrameLoad.machine (fun _ : Fin 5 => 0) extras _ _ base hr
  have hl := TapeRenaming.run_rename layout (TapeEmbedding.machine 5 FrameLoad.machine) _ _ _ he
  let first := TapeRenaming.receipt layout (TapeEmbedding.receipt (fun _ : Fin 5 => 0) extras base)
  have hi : TapeRenaming.config layout (TapeEmbedding.config (fun _ : Fin 5 => 0) extras
      (CellLoad.loaderInput source pre.length recordBacking (word ++ rank).length)) =
      config load.start (workspace word rank recordBacking cloneBacking rankBacking) source pre.length := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, CellLoad.loaderInput, config, Fin.addCases]
    · funext i
      fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, CellLoad.loaderInput, config,
        workspace, RecordExtractReset.input, RecordExtract.input, RecordClone.input, RecordClone.raw, extras, Fin.addCases]
  have hl' : runFrom load (4 * (word ++ rank).length + 3)
      (config load.start (workspace word rank recordBacking cloneBacking rankBacking) source pre.length) = some first := by
    rw [← hi]
    exact hl
  obtain ⟨extracted, hx, hxc, hxt, hxh, hxs, hxp⟩ := RecordExtractReset.reset_run word rank cloneBacking rankBacking hw hclone hrank
  have hxe := TapeEmbedding.run_embed RecordExtractReset.machine (fun _ : Fin 1 => next) (fun _ => source) _ _ extracted hx
  let second := TapeEmbedding.receipt (fun _ : Fin 1 => next) (fun _ => source) extracted
  have hmid : Composition.restart first.final extract.start =
      TapeEmbedding.config (fun _ : Fin 1 => next) (fun _ => source)
        (initialConfiguration RecordExtractReset.machine (RecordExtractReset.input word rank cloneBacking rankBacking)) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.restart, first, TapeRenaming.receipt, TapeRenaming.config,
        TapeEmbedding.receipt, TapeEmbedding.config, hf, FrameLoad.reset, initialConfiguration, next, hlen, Fin.addCases]
      omega
    · funext i
      fin_cases i <;> simp [Composition.restart, first, TapeRenaming.receipt, TapeRenaming.config,
        TapeEmbedding.receipt, TapeEmbedding.config, hf, FrameLoad.reset, initialConfiguration,
        RecordExtractReset.input, RecordExtract.input, RecordClone.input, RecordClone.raw, extras, source, Fin.addCases]
  have hxe' : runFrom extract (48 * word.length + 30) (Composition.restart first.final extract.start) = some second := by
    rw [hmid]
    exact hxe
  have hj := Composition.run_join load extract (4 * (word ++ rank).length + 3) (48 * word.length + 30)
    (config load.start (workspace word rank recordBacking cloneBacking rankBacking) source pre.length) first second hl' hxe'
  have htime : (4 * (word ++ rank).length + 3) + 1 + (48 * word.length + 30) = 56 * word.length + 34 := by rw [hlen]; omega
  refine ⟨Composition.joinedReceipt first second, by rw [htime] at hj; exact hj, ?_, ?_, ?_⟩
  · apply configuration_ext
    · change extracted.final.control.natAdd 4 = (20 : Fin 21)
      rw [hxc]
      decide
    · funext i
      fin_cases i <;> simp [Composition.joinedReceipt, Composition.rightConfig, second, TapeEmbedding.receipt,
        TapeEmbedding.config, config, hxh, next, Fin.addCases]
    · simp [Composition.joinedReceipt, Composition.rightConfig, second, TapeEmbedding.receipt,
        TapeEmbedding.config, config, hxt, source]
  · change base.steps + 1 + extracted.steps = _
    rw [hlen] at hs
    omega
  · change max (base.peakTapeCells + TapeEmbedding.extraCells extras)
      (extracted.peakTapeCells + TapeEmbedding.extraCells (fun _ : Fin 1 => source)) ≤ _
    simp [TapeEmbedding.extraCells, extras, Fin.sum_univ_succ, hlen]
    dsimp only [source]
    simp only [List.length_append, frame_length, hw] at hp ⊢
    omega

end NearCubicWires.RepairOrdinary.RecordLoad
