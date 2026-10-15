import Proof.MachineModel.OrdinaryFrameLoad

/-! Load a framed rank from an advancing source stream, then execute the
reusable cell emitter. Both global cursors survive the bounded local work. -/
namespace NearCubicWires.RepairOrdinary.CellLoad
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def loaderInput (source : List Bool) (position : ℕ) (backing : List Bool) (width : ℕ) : Configuration 3 4 :=
  ⟨0, ![position, 0, 0], ![source, backing, List.replicate (2 * width + 1) false]⟩

theorem loader_run (pre bits suffix backing : List Bool) (hb : backing.length ≤ 2 * bits.length + 1) :
    ∃ r : ExecutionReceipt 3 4,
      runFrom FrameLoad.machine (4 * bits.length + 3)
        (loaderInput (pre ++ frame bits ++ suffix) pre.length backing bits.length) = some r ∧
      r.final = FrameLoad.reset 3 (pre ++ frame bits ++ suffix) (pre.length + 2 * bits.length + 1)
        (frame bits) 0 (2 * bits.length + 1) ∧ r.steps = 4 * bits.length + 3 ∧
      r.peakTapeCells ≤ (pre ++ frame bits ++ suffix).length + 8 * bits.length + 4 := by
  obtain ⟨base, hbRun, hbf, hbs, hbp⟩ := FrameLoad.load_run pre bits suffix backing hb
  let caps : Fin 3 → ℕ := ![0, 0, 2 * bits.length + 1]
  obtain ⟨r, hr, hf, hs, hp⟩ := ZeroPadding.run_config FrameLoad.machine caps _ _ base hbRun
  have hi : ZeroPadding.config caps (FrameLoad.scan 0 (pre ++ frame bits ++ suffix) pre.length [] backing) =
      loaderInput (pre ++ frame bits ++ suffix) pre.length backing bits.length := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config, caps, FrameLoad.scan, loaderInput,
        StablePartition.Workspace.overlay, ZeroPadding.pad]
  have he : ZeroPadding.config caps (FrameLoad.reset 3 (pre ++ frame bits ++ suffix)
      (pre.length + 2 * bits.length + 1) (frame bits) 0 (2 * bits.length + 1)) =
      FrameLoad.reset 3 (pre ++ frame bits ++ suffix) (pre.length + 2 * bits.length + 1)
        (frame bits) 0 (2 * bits.length + 1) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config, caps, FrameLoad.reset, ZeroPadding.pad]
  refine ⟨r, by rw [hi] at hr; exact hr, by rw [hf, hbf, he], hs.trans hbs, ?_⟩
  simp [ZeroPadding.cells, caps, Fin.sum_univ_succ] at hp
  omega

def layout : Fin 10 ≃ Fin 10 where
  toFun := ![9, 4, 3, 0, 1, 2, 5, 6, 7, 8]
  invFun := ![3, 4, 5, 2, 1, 6, 7, 8, 9, 0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem layout_inverse : (layout.symm : Fin 10 → Fin 10) = ![3, 4, 5, 2, 1, 6, 7, 8, 9, 0] := rfl

def loader : Machine 10 4 := TapeRenaming.machine layout (TapeEmbedding.machine 7 FrameLoad.machine)
def emitter : Machine 10 20 := TapeEmbedding.machine 1 CellEmit.machine
def machine : Machine 10 24 := Composition.machine loader emitter
def config {s : ℕ} (state : Fin s) (width a b rank : ℕ) (backing : List Bool) (mask : Bool)
    (source : List Bool) (position : ℕ) (out : List Bool) : Configuration 10 s :=
  TapeEmbedding.config (fun _ : Fin 1 => position) (fun _ => source)
    (CellEmit.config state (LocalCell.input width a b rank backing mask) out)

theorem body_run (width a b rank oldRank : ℕ) (pre suffix backing out : List Bool) (mask : Bool)
    (hfit : a + b < 2 ^ width) (hrank : rank < 2 ^ width) (hb : backing.length ≤ 2 * width + 1) :
    ∃ r : ExecutionReceipt 10 24,
      runFrom machine (16 * width + 20)
        (config machine.start width a b oldRank backing mask (pre ++ frame (binary width rank) ++ suffix) pre.length out) = some r ∧
      r.final = config 23 width a b rank (frame (binary width (a + b))) mask
        (pre ++ frame (binary width rank) ++ suffix) (pre.length + 2 * width + 1)
        (out ++ [LeftCell.selected a b rank mask]) ∧
      r.steps = 16 * width + 20 ∧
      r.peakTapeCells ≤ (pre ++ frame (binary width rank) ++ suffix).length + 26 * width + out.length + 22 := by
  let source := pre ++ frame (binary width rank) ++ suffix
  let next := pre.length + 2 * width + 1
  obtain ⟨base, hr, hf, hs, hp⟩ := loader_run pre (binary width rank) suffix (frame (binary width oldRank)) (by simp)
  simp only [binary_length] at hr hf hs hp
  let otherHeads : Fin 7 → ℕ := ![0, 0, 0, 0, 0, 0, out.length]
  let otherTapes : Fin 7 → List Bool := ![frame (binary width a), frame (binary width b), backing,
    [false], [mask], List.replicate (6 * width + 6) false, out]
  have he := TapeEmbedding.run_embed FrameLoad.machine otherHeads otherTapes _ _ base hr
  have hl := TapeRenaming.run_rename layout (TapeEmbedding.machine 7 FrameLoad.machine) _ _ _ he
  let first := TapeRenaming.receipt layout (TapeEmbedding.receipt otherHeads otherTapes base)
  have hi : TapeRenaming.config layout (TapeEmbedding.config otherHeads otherTapes
      (loaderInput source pre.length (frame (binary width oldRank)) width)) =
      config loader.start width a b oldRank backing mask source pre.length out := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, loaderInput, config,
        CellEmit.config, otherHeads, Fin.addCases]
    · funext i
      fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, loaderInput, config,
        CellEmit.config, LocalCell.input, LocalCell.raw, otherTapes, Fin.addCases]
  have hl' : runFrom loader (4 * width + 3) (config loader.start width a b oldRank backing mask source pre.length out) = some first := by
    rw [← hi]
    exact hl
  obtain ⟨cell, hc, hcf, hcs, hcp⟩ := CellEmit.cell_run width a b rank backing out mask hfit hrank hb
  have hce := TapeEmbedding.run_embed CellEmit.machine (fun _ : Fin 1 => next) (fun _ => source) _ _ cell hc
  let second := TapeEmbedding.receipt (fun _ : Fin 1 => next) (fun _ => source) cell
  have hmid : Composition.restart first.final emitter.start =
      TapeEmbedding.config (fun _ : Fin 1 => next) (fun _ => source)
        (CellEmit.config CellEmit.machine.start (LocalCell.input width a b rank backing mask) out) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.restart, first, TapeRenaming.receipt, TapeRenaming.config,
        TapeEmbedding.receipt, TapeEmbedding.config, hf, FrameLoad.reset, CellEmit.config, otherHeads, next, Fin.addCases]
    · funext i
      fin_cases i <;> simp [Composition.restart, first, TapeRenaming.receipt, TapeRenaming.config,
        TapeEmbedding.receipt, TapeEmbedding.config, hf, FrameLoad.reset, CellEmit.config,
        LocalCell.input, LocalCell.raw, otherTapes, source, Fin.addCases]
  have hce' : runFrom emitter (12 * width + 16) (Composition.restart first.final emitter.start) = some second := by
    rw [hmid]
    exact hce
  have hj := Composition.run_join loader emitter (4 * width + 3) (12 * width + 16)
    (config loader.start width a b oldRank backing mask source pre.length out) first second hl' hce'
  have htime : (4 * width + 3) + 1 + (12 * width + 16) = 16 * width + 20 := by omega
  refine ⟨Composition.joinedReceipt first second, by rw [htime] at hj; exact hj, ?_, ?_, ?_⟩
  · apply configuration_ext
    · change cell.final.control.natAdd 4 = (23 : Fin 24)
      rw [hcf]
      change (19 : Fin 20).natAdd 4 = (23 : Fin 24)
      decide
    · funext i
      fin_cases i <;> simp [Composition.joinedReceipt, Composition.rightConfig, second, TapeEmbedding.receipt,
        TapeEmbedding.config, hcf, CellEmit.config, config, next, Fin.addCases]
    · funext i
      fin_cases i <;> simp [Composition.joinedReceipt, Composition.rightConfig, second, TapeEmbedding.receipt,
        TapeEmbedding.config, hcf, CellEmit.config, CellEmit.cleared, LocalCell.output,
        config, LocalCell.input, LocalCell.raw, source, Fin.addCases]
  · change base.steps + 1 + cell.steps = _
    omega
  · change max (base.peakTapeCells + TapeEmbedding.extraCells otherTapes)
      (cell.peakTapeCells + TapeEmbedding.extraCells (fun _ : Fin 1 => source)) ≤ _
    simp [TapeEmbedding.extraCells, otherTapes, Fin.sum_univ_succ]
    dsimp only [source]
    simp only [List.length_append, frame_length, binary_length] at hp ⊢
    omega

end NearCubicWires.RepairOrdinary.CellLoad
