import Proof.MachineModel.OrdinaryMemoryCompare
import Proof.MachineModel.OrdinaryMemoryDecision

/-! One complete actual sorted-memory record check: load/extract, compare,
check the read bit, and retain the new written value. The following iteration
still must copy the current key and reset bounded work heads; no global source
rewind is part of this operation. -/
namespace NearCubicWires.RepairOrdinary.MemoryCheck
open LocalBitMultitape MemoryLog MemorySort MemoryCompare StablePartition SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def layout : Fin 11 ≃ Fin 11 where
  toFun := ![0, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8]
  invFun := ![0, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem layout_inverse : (layout.symm : Fin 11 → Fin 11) =
    ![0, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2] := rfl
def decideRecord : Machine 11 5 :=
  TapeRenaming.machine layout (TapeEmbedding.machine 8 MemoryDecision.machine)
def machine : Machine 11 31 := Composition.machine MemoryCompare.machine decideRecord

def passed (previous current : Event) : Bool :=
  decide (current.read = MemoryScan.memory previous current.cell)

def completed {s : ℕ} (state : Fin s) (I W timestamp : ℕ) (previous current : Event)
    (source : List Bool) (position : ℕ) (out : List Bool) : Configuration 11 s :=
  { MemoryCompare.finished state (I+2)
      (RecordExtractReset.output (front I timestamp current) (key I W current))
      source position (key I W previous) current.after (out ++ [passed previous current]) with
    heads := ![3, 0, 0, 0, 2*(I+2), 0, 0, position, 2*(I+2), 0, out.length] }

theorem record_run (I W timestamp : ℕ) (previous current : Event)
    (pre suffix recordBacking cloneBacking rankBacking out : List Bool)
    (hrecord : recordBacking.length ≤ 4*(I+2)+1)
    (hclone : cloneBacking.length ≤ 4*(I+2)+1)
    (hrank : rankBacking.length ≤ 2*(I+2)+1)
    (hp : cellCode W previous.cell < 2^(I+2))
    (hc : cellCode W current.cell < 2^(I+2))
    (hap : previous.cell.2 < 2^W) (hac : current.cell.2 < 2^W)
    (order : cellCode W previous.cell ≤ cellCode W current.cell) :
    ∃ r : ExecutionReceipt 11 31,
      runFrom machine (58*(I+2)+41)
        (MemoryCompare.config machine.start
          (RecordLoad.workspace (front I timestamp current) (key I W current)
            recordBacking cloneBacking rankBacking)
          (pre ++ recordBits (encoded I (I+2) W timestamp current) ++ suffix) pre.length
          (key I W previous) previous.after out) = some r ∧
      r.final = completed 30 I W timestamp previous current
        (pre ++ recordBits (encoded I (I+2) W timestamp current) ++ suffix)
        (pre.length+4*(I+2)+1) out ∧ r.steps = 58*(I+2)+41 := by
  obtain ⟨first, hf, hff, hfs⟩ := load_compare_run I W timestamp previous current
    pre suffix recordBacking cloneBacking rankBacking out hrecord hclone hrank hp hc hap hac order
  let source := pre ++ recordBits (encoded I (I+2) W timestamp current) ++ suffix
  let next := pre.length+4*(I+2)+1
  let workspace := RecordExtractReset.output (front I timestamp current) (key I W current)
  let same := decide (current.cell = previous.cell)
  obtain ⟨decision, hd, hdf, hds⟩ := MemoryDecision.decision_run
    current.read current.after previous.after same (binary I timestamp ++ key I W current) out
  have hpass : MemoryDecision.accept current.read previous.after same = passed previous current :=
    MemoryDecision.accept_memory previous current
  rw [hpass] at hdf
  let otherHeads : Fin 8 → ℕ := ![0, 0, 0, 2*(I+2), 0, 0, next, 2*(I+2)]
  let otherTapes : Fin 8 → List Bool :=
    ![workspace 1, workspace 2, workspace 3, workspace 4, workspace 5, workspace 6,
      source, frame (key I W previous)]
  have he := TapeEmbedding.run_embed MemoryDecision.machine otherHeads otherTapes _ _ decision hd
  have hr := TapeRenaming.run_rename layout (TapeEmbedding.machine 8 MemoryDecision.machine) _ _ _ he
  let second := TapeRenaming.receipt layout (TapeEmbedding.receipt otherHeads otherTapes decision)
  have hmid : Composition.restart first.final decideRecord.start =
      TapeRenaming.config layout (TapeEmbedding.config otherHeads otherTapes
        (MemoryDecision.config 0
          (frame (current.read :: current.after :: (binary I timestamp ++ key I W current)))
          0 previous.after (out ++ [same]) (out.length+1))) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.restart, hff, MemoryCompare.finished,
        TapeRenaming.config, TapeEmbedding.config, MemoryDecision.config, otherHeads, next, Fin.addCases]
    · funext i
      fin_cases i <;> simp [Composition.restart, hff, MemoryCompare.finished,
        TapeRenaming.config, TapeEmbedding.config, MemoryDecision.config, otherTapes,
        workspace, RecordExtractReset.output, RecordExtract.finished, front, source, same, Fin.addCases]
  have hsecond : runFrom decideRecord 4 (Composition.restart first.final decideRecord.start) = some second := by
    rw [hmid]
    exact hr
  have hj := Composition.run_join MemoryCompare.machine decideRecord (58*(I+2)+36) 4
    (MemoryCompare.config MemoryCompare.machine.start
      (RecordLoad.workspace (front I timestamp current) (key I W current)
        recordBacking cloneBacking rankBacking) source pre.length (key I W previous) previous.after out)
    first second hf hsecond
  have htime : (58*(I+2)+36)+1+4 = 58*(I+2)+41 := by omega
  refine ⟨Composition.joinedReceipt first second, ?_, ?_, ?_⟩
  · rw [htime] at hj
    exact hj
  · apply configuration_ext
    · change decision.final.control.natAdd 26 = (30 : Fin 31)
      rw [hdf]
      rfl
    · funext i
      fin_cases i <;> simp [Composition.joinedReceipt, Composition.rightConfig, second,
        TapeRenaming.receipt, TapeRenaming.config, TapeEmbedding.receipt, TapeEmbedding.config,
        hdf, MemoryDecision.config, completed, otherHeads, next, Fin.addCases]
    · funext i
      fin_cases i <;> simp [Composition.joinedReceipt, Composition.rightConfig, second,
        TapeRenaming.receipt, TapeRenaming.config, TapeEmbedding.receipt, TapeEmbedding.config,
        hdf, MemoryDecision.config, completed, MemoryCompare.finished, otherTapes, workspace,
        RecordExtractReset.output, RecordExtract.finished, front, source, Fin.addCases]
  · change first.steps+1+decision.steps = _
    omega

end NearCubicWires.RepairOrdinary.MemoryCheck
