import Proof.MachineModel.OrdinaryMemoryCheck
import Proof.MachineModel.OrdinaryMaskedReset

/-! Reusable record body for the sorted-memory loop. Check one
record, reset only bounded local heads, retain its key, and reset the copy
source. Both global stream cursors survive. The loop controller still pays
for advancing the validity cursor and for final acceptance. -/
namespace NearCubicWires.RepairOrdinary.MemoryCycle
open LocalBitMultitape MemoryLog MemorySort MemoryCompare StablePartition SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def checkCap (I : ℕ) : ℕ := 58*(I+2)+41
def copyCap (I : ℕ) : ℕ := 120*(I+2)+88
def selected (i : Fin 11) : Bool := i.val == 0 || i.val == 4 || i.val == 8
def check : Machine 12 33 := MaskedReset.machine MemoryCheck.machine selected
def layout : Fin 12 ≃ Fin 12 where
  toFun := ![4, 8, 5, 0, 1, 2, 3, 6, 7, 9, 10, 11]
  invFun := ![3, 4, 5, 6, 0, 2, 7, 8, 1, 9, 10, 11]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem layout_inverse : (layout.symm : Fin 12 → Fin 12) =
    ![3, 4, 5, 6, 0, 2, 7, 8, 1, 9, 10, 11] := rfl
def copy : Machine 12 4 := TapeRenaming.machine layout (TapeEmbedding.machine 9 FrameLoad.machine)
def joined : Machine 12 37 := Composition.machine check copy
def machine : Machine 13 39 := SelectiveReset.machine joined 4

def config {s : ℕ} (state : Fin s) (I : ℕ) (workspace : Fin 7 → List Bool)
    (source : List Bool) (position : ℕ) (previousKey : List Bool) (previousAfter : Bool)
    (out : List Bool) (flagPosition : ℕ) : Configuration 12 s :=
  ⟨state, ![0, 0, 0, 0, 0, 0, 0, position, 0, 0, flagPosition, 0],
    ![workspace 0, workspace 1, workspace 2, workspace 3, workspace 4, workspace 5, workspace 6,
      source, frame previousKey, [previousAfter], out, List.replicate (checkCap I) false]⟩
def ready {s : ℕ} (state : Fin s) (I : ℕ) (workspace : Fin 7 → List Bool)
    (source : List Bool) (position : ℕ) (previousKey : List Bool) (previousAfter : Bool)
    (out : List Bool) (flagPosition : ℕ) : Configuration 13 s :=
  TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ => List.replicate (copyCap I) false)
    (config state I workspace source position previousKey previousAfter out flagPosition)

theorem check_run (I W timestamp : ℕ) (previous current : Event)
    (pre suffix recordBacking cloneBacking rankBacking out : List Bool)
    (hrecord : recordBacking.length ≤ 4*(I+2)+1)
    (hclone : cloneBacking.length ≤ 4*(I+2)+1)
    (hrank : rankBacking.length ≤ 2*(I+2)+1)
    (hp : cellCode W previous.cell < 2^(I+2))
    (hc : cellCode W current.cell < 2^(I+2))
    (hap : previous.cell.2 < 2^W) (hac : current.cell.2 < 2^W)
    (order : cellCode W previous.cell ≤ cellCode W current.cell) :
    ∃ r : ExecutionReceipt 12 33,
      runFrom check (116*(I+2)+84)
        (config check.start I
          (RecordLoad.workspace (front I timestamp current) (key I W current)
            recordBacking cloneBacking rankBacking)
          (pre ++ recordBits (encoded I (I+2) W timestamp current) ++ suffix) pre.length
          (key I W previous) previous.after out out.length) = some r ∧
      r.final = config 32 I (RecordExtractReset.output (front I timestamp current) (key I W current))
        (pre ++ recordBits (encoded I (I+2) W timestamp current) ++ suffix)
        (pre.length+4*(I+2)+1) (key I W previous) current.after
        (out ++ [MemoryCheck.passed previous current]) out.length ∧ r.steps = 116*(I+2)+84 := by
  obtain ⟨base, hb, hf, hs⟩ := MemoryCheck.record_run I W timestamp previous current
    pre suffix recordBacking cloneBacking rankBacking out hrecord hclone hrank hp hc hap hac order
  have hstart : ∀ i, selected i = true →
      (MemoryCompare.config MemoryCheck.machine.start
        (RecordLoad.workspace (front I timestamp current) (key I W current)
          recordBacking cloneBacking rankBacking)
        (pre ++ recordBits (encoded I (I+2) W timestamp current) ++ suffix) pre.length
        (key I W previous) previous.after out).heads i = 0 := by
    intro i hi
    fin_cases i <;> simp_all [selected, MemoryCompare.config, RecordLoad.config, TapeEmbedding.config, Fin.addCases]
  obtain ⟨r, hr, hfinal, hsteps, _⟩ := MaskedReset.workspace_run MemoryCheck.machine selected
    (checkCap I) (checkCap I) _ base hb hstart (by dsimp [checkCap]; omega)
  refine ⟨r, ?_, ?_, by omega⟩
  · have hi : ZeroPadding.config (Rewind.Workspace.capacities 11 (checkCap I))
        (Rewind.recording (MemoryCompare.config MemoryCheck.machine.start
          (RecordLoad.workspace (front I timestamp current) (key I W current)
            recordBacking cloneBacking rankBacking)
          (pre ++ recordBits (encoded I (I+2) W timestamp current) ++ suffix) pre.length
          (key I W previous) previous.after out) 0) =
        config check.start I
          (RecordLoad.workspace (front I timestamp current) (key I W current)
            recordBacking cloneBacking rankBacking)
          (pre ++ recordBits (encoded I (I+2) W timestamp current) ++ suffix) pre.length
          (key I W previous) previous.after out out.length := by
      apply configuration_ext
      · rfl
      · funext i
        fin_cases i <;> simp [ZeroPadding.config, Rewind.recording, Rewind.config, config,
          MemoryCompare.config, RecordLoad.config, TapeEmbedding.config, Fin.addCases]
      · funext i
        fin_cases i <;> simp [ZeroPadding.config, ZeroPadding.pad, Rewind.Workspace.capacities,
          Rewind.recording, Rewind.config, config, MemoryCompare.config, RecordLoad.config,
          TapeEmbedding.config, Fin.addCases]
    rw [hi, hs] at hr
    have htime : 2*(58*(I+2)+41)+2 = 116*(I+2)+84 := by omega
    rw [htime] at hr
    exact hr
  · rw [hfinal, hf]
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [SelectiveReset.finished, Rewind.config, config, selected, MemoryCheck.completed,
        Fin.addCases]
    · funext i
      fin_cases i <;> simp [SelectiveReset.finished, Rewind.config, config,
        MemoryCheck.completed, MemoryCompare.finished, Fin.addCases]

theorem copy_run (I W timestamp : ℕ) (previous current : Event)
    (source out : List Bool) (position flagPosition : ℕ) :
    ∃ r : ExecutionReceipt 12 4,
      runFrom copy (4*(I+2)+3)
        (config copy.start I (RecordExtractReset.output (front I timestamp current) (key I W current))
          source position (key I W previous) current.after out flagPosition) = some r ∧
      r.final = { config (3 : Fin 4) I (RecordExtractReset.output (front I timestamp current) (key I W current))
          source position (key I W current) current.after out flagPosition with
        heads := Function.update (config (3 : Fin 4) I
          (RecordExtractReset.output (front I timestamp current) (key I W current))
          source position (key I W current) current.after out flagPosition).heads 4 (2*(I+2)+1) } ∧
      r.steps = 4*(I+2)+3 := by
  let workspace := RecordExtractReset.output (front I timestamp current) (key I W current)
  obtain ⟨base, hb, hf, hs, _⟩ := CellLoad.loader_run [] (key I W current) []
    (frame (key I W previous)) (by simp)
  simp only [List.nil_append, List.append_nil, List.length_nil, zero_add, key_length] at hb hf hs
  let otherHeads : Fin 9 → ℕ := ![0, 0, 0, 0, 0, position, 0, flagPosition, 0]
  let otherTapes : Fin 9 → List Bool := ![workspace 0, workspace 1, workspace 2, workspace 3,
    workspace 6, source, [current.after], out, List.replicate (checkCap I) false]
  have he := TapeEmbedding.run_embed FrameLoad.machine otherHeads otherTapes _ _ base hb
  have hr := TapeRenaming.run_rename layout (TapeEmbedding.machine 9 FrameLoad.machine) _ _ _ he
  let r := TapeRenaming.receipt layout (TapeEmbedding.receipt otherHeads otherTapes base)
  have hi : TapeRenaming.config layout (TapeEmbedding.config otherHeads otherTapes
      (CellLoad.loaderInput (frame (key I W current)) 0 (frame (key I W previous)) (I+2))) =
      config copy.start I workspace source position (key I W previous) current.after out flagPosition := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, CellLoad.loaderInput,
        config, otherHeads, Fin.addCases]
    · funext i
      fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, CellLoad.loaderInput,
        config, otherTapes, workspace, RecordExtractReset.output, RecordExtract.finished, Fin.addCases]
  refine ⟨r, by rw [hi] at hr; exact hr, ?_, hs⟩
  apply configuration_ext
  · change base.final.control = (3 : Fin 4)
    rw [hf]
    rfl
  · funext i
    fin_cases i <;> simp [r, TapeRenaming.receipt, TapeRenaming.config, TapeEmbedding.receipt,
      TapeEmbedding.config, hf, FrameLoad.reset, config, otherHeads, Fin.addCases]
  · funext i
    fin_cases i <;> simp [r, TapeRenaming.receipt, TapeRenaming.config, TapeEmbedding.receipt,
      TapeEmbedding.config, hf, FrameLoad.reset, config, otherTapes, workspace,
      RecordExtractReset.output, RecordExtract.finished, Fin.addCases]

theorem joined_run (I W timestamp : ℕ) (previous current : Event)
    (pre suffix recordBacking cloneBacking rankBacking out : List Bool)
    (hrecord : recordBacking.length ≤ 4*(I+2)+1)
    (hclone : cloneBacking.length ≤ 4*(I+2)+1)
    (hrank : rankBacking.length ≤ 2*(I+2)+1)
    (hp : cellCode W previous.cell < 2^(I+2))
    (hc : cellCode W current.cell < 2^(I+2))
    (hap : previous.cell.2 < 2^W) (hac : current.cell.2 < 2^W)
    (order : cellCode W previous.cell ≤ cellCode W current.cell) :
    ∃ r : ExecutionReceipt 12 37,
      runFrom joined (copyCap I)
        (config joined.start I
          (RecordLoad.workspace (front I timestamp current) (key I W current)
            recordBacking cloneBacking rankBacking)
          (pre ++ recordBits (encoded I (I+2) W timestamp current) ++ suffix) pre.length
          (key I W previous) previous.after out out.length) = some r ∧
      r.final = { config (36 : Fin 37) I
          (RecordExtractReset.output (front I timestamp current) (key I W current))
          (pre ++ recordBits (encoded I (I+2) W timestamp current) ++ suffix)
          (pre.length+4*(I+2)+1) (key I W current) current.after
          (out ++ [MemoryCheck.passed previous current]) out.length with
        heads := Function.update (config (36 : Fin 37) I
          (RecordExtractReset.output (front I timestamp current) (key I W current))
          (pre ++ recordBits (encoded I (I+2) W timestamp current) ++ suffix)
          (pre.length+4*(I+2)+1) (key I W current) current.after
          (out ++ [MemoryCheck.passed previous current]) out.length).heads 4 (2*(I+2)+1) } ∧
      r.steps = copyCap I := by
  obtain ⟨first, hf, hff, hfs⟩ := check_run I W timestamp previous current pre suffix
    recordBacking cloneBacking rankBacking out hrecord hclone hrank hp hc hap hac order
  let source := pre ++ recordBits (encoded I (I+2) W timestamp current) ++ suffix
  let next := pre.length+4*(I+2)+1
  let workspace := RecordExtractReset.output (front I timestamp current) (key I W current)
  let flags := out ++ [MemoryCheck.passed previous current]
  obtain ⟨second, hs, hsf, hss⟩ := copy_run I W timestamp previous current source flags next out.length
  have hmid : Composition.restart first.final copy.start =
      config copy.start I workspace source next (key I W previous) current.after flags out.length := by
    rw [hff]
    rfl
  have hs' : runFrom copy (4*(I+2)+3) (Composition.restart first.final copy.start) = some second := by
    rw [hmid]
    exact hs
  have hj := Composition.run_join check copy (116*(I+2)+84) (4*(I+2)+3)
    (config check.start I
      (RecordLoad.workspace (front I timestamp current) (key I W current)
        recordBacking cloneBacking rankBacking)
      source pre.length (key I W previous) previous.after out out.length) first second hf hs'
  have htime : (116*(I+2)+84)+1+(4*(I+2)+3) = copyCap I := by dsimp [copyCap]; omega
  refine ⟨Composition.joinedReceipt first second, ?_, ?_, ?_⟩
  · rw [htime] at hj
    exact hj
  · rw [Composition.joinedReceipt, hsf]
    rfl
  · change first.steps+1+second.steps = _
    rw [hfs, hss]
    exact htime

/-- Entire paid check/reset/copy/reset body. Its two global cursors are kept:
source7 advances one record and flag10 still points to the newly written flag.
The loop pays the final one-cell flag advance separately. -/
theorem cycle_run (I W timestamp : ℕ) (previous current : Event)
    (pre suffix recordBacking cloneBacking rankBacking out : List Bool)
    (hrecord : recordBacking.length ≤ 4*(I+2)+1)
    (hclone : cloneBacking.length ≤ 4*(I+2)+1)
    (hrank : rankBacking.length ≤ 2*(I+2)+1)
    (hp : cellCode W previous.cell < 2^(I+2))
    (hc : cellCode W current.cell < 2^(I+2))
    (hap : previous.cell.2 < 2^W) (hac : current.cell.2 < 2^W)
    (order : cellCode W previous.cell ≤ cellCode W current.cell) :
    ∃ r : ExecutionReceipt 13 39,
      runFrom machine (2*copyCap I+2)
        (ready machine.start I
          (RecordLoad.workspace (front I timestamp current) (key I W current)
            recordBacking cloneBacking rankBacking)
          (pre ++ recordBits (encoded I (I+2) W timestamp current) ++ suffix) pre.length
          (key I W previous) previous.after out out.length) = some r ∧
      r.final = ready 38 I (RecordExtractReset.output (front I timestamp current) (key I W current))
        (pre ++ recordBits (encoded I (I+2) W timestamp current) ++ suffix)
        (pre.length+4*(I+2)+1) (key I W current) current.after
        (out ++ [MemoryCheck.passed previous current]) out.length ∧
      r.steps = 2*copyCap I+2 := by
  obtain ⟨body, hb, hbf, hbs⟩ := joined_run I W timestamp previous current pre suffix
    recordBacking cloneBacking rankBacking out hrecord hclone hrank hp hc hap hac order
  obtain ⟨r, hr, hf, hs, _⟩ := SelectiveReset.workspace_run joined (4 : Fin 12)
    (copyCap I) (copyCap I) _ body hb (by rfl) (by omega)
  refine ⟨r, ?_, ?_, by omega⟩
  · have hi : ZeroPadding.config (Rewind.Workspace.capacities 12 (copyCap I))
        (Rewind.recording (config joined.start I
          (RecordLoad.workspace (front I timestamp current) (key I W current)
            recordBacking cloneBacking rankBacking)
          (pre ++ recordBits (encoded I (I+2) W timestamp current) ++ suffix) pre.length
          (key I W previous) previous.after out out.length) 0) =
        ready machine.start I
          (RecordLoad.workspace (front I timestamp current) (key I W current)
            recordBacking cloneBacking rankBacking)
          (pre ++ recordBits (encoded I (I+2) W timestamp current) ++ suffix) pre.length
          (key I W previous) previous.after out out.length := by
      apply configuration_ext
      · rfl
      · rfl
      · funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
          simp [ZeroPadding.config, Rewind.Workspace.capacities, Rewind.recording,
            Rewind.config, ready, TapeEmbedding.config, ZeroPadding.pad]
        all_goals rfl
    rw [hi, hbs] at hr
    exact hr
  · rw [hf, hbf]
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · fin_cases j <;> simp [SelectiveReset.finished, Rewind.config, ready,
          TapeEmbedding.config, config, Fin.addCases]
      · simp [SelectiveReset.finished, Rewind.config, ready, TapeEmbedding.config]
    · rfl

end NearCubicWires.RepairOrdinary.MemoryCycle
