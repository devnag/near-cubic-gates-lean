import Proof.Supplier.RowOccurrenceAppend
import Proof.Supplier.RowOccurrenceClear

/-! Repeated occurrence call on the same24-tape bank. The child index is
physically cleared with the existing capacity driver, while the ordered
occurrence cursor and both coefficient append cursors remain advanced. -/
namespace NearCubicWires.RepairOrdinary.RowOccurrenceReusable
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def caps (D : ℕ) (a : Fin 24) := if a=19 then D else 0
noncomputable def machine := Composition.machine RowOccurrenceAppend.machine RowOccurrenceClear.machine
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) (j w C D : ℕ)
    (source : List Bool) (pos : ℕ) (positive negative : List Bool) :=
  Composition.leftConfig 6 (ZeroPadding.config (caps D)
    (RowOccurrenceAppend.entry gs j w C D source pos positive negative))
noncomputable def padded {n : ℕ} (gs : List (ExactThresholdGate n)) (i j w C D : ℕ)
    (source : List Bool) (pos : ℕ) (positive negative : List Bool) :=
  ZeroPadding.config (caps D) (RowOccurrenceAppend.ready gs i j w C D source pos positive negative)
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i<gs.length)
    (j : ℕ) (hj : j≤n) (w C D : ℕ) := RowOccurrenceAppend.budget gs i hi j hj w C D+2*D+7

theorem pad_index {n : ℕ} (gs : List (ExactThresholdGate n)) (i j w C D : ℕ)
    (source : List Bool) (pos : ℕ) (positive negative : List Bool) :
    (padded gs i j w C D source pos positive negative).heads 19=1 ∧
    (padded gs i j w C D source pos positive negative).heads 21=0 ∧
    (padded gs i j w C D source pos positive negative).heads 22=0 ∧
    (padded gs i j w C D source pos positive negative).tapes 19=ZeroPadding.pad D (UnaryTemplate.tape i) ∧
    (padded gs i j w C D source pos positive negative).tapes 21=List.replicate D true ∧
    (padded gs i j w C D source pos positive negative).tapes 22=List.replicate (D+1) false := by
  simp [padded,ZeroPadding.config,caps,RowOccurrenceAppend.ready,
    RowCachedCoordinateReusable.entry,RowCachedCoordinateReusable.extended,
    Composition.leftConfig,TapeEmbedding.config,RowCachedCoordinateReset.entry,
    Rewind.recording,Rewind.config,RowCachedCoordinateReset.caps,
    RowCachedCoordinateAppend.entry,RowCachedCoordinateAppend.ready,
    RowCachedCoordinateAppend.extra,Fin.addCases,RowCachedCoordinateReusable.extra,ZeroPadding.pad]

theorem cleared_heads {n : ℕ} (gs : List (ExactThresholdGate n)) (i j w C D : ℕ)
    (source : List Bool) (pos : ℕ) (positive negative : List Bool) :
    RowOccurrenceClear.heads (padded gs i j w C D source pos positive negative).heads=
      (entry gs j w C D source pos positive negative).heads := by
  funext a
  by_cases ha : a=19
  · subst a; simp [RowOccurrenceClear.heads,entry,RowOccurrenceAppend.entry,
      RowOccurrenceAppend.blank,Composition.leftConfig,Composition.restart,ZeroPadding.config]
  have he := (RowOccurrenceAppend.ready_except_index gs i j w C D source pos positive negative a ha).1
  simpa [RowOccurrenceClear.heads,padded,entry,RowOccurrenceAppend.entry,
    RowOccurrenceAppend.blank,Composition.leftConfig,Composition.restart,ZeroPadding.config,ha] using he

theorem clear_pick (a : Fin 24) : RecoveryFocus.pick RowOccurrenceClear.slots a=
    (if a=19 then some 0 else if a=21 then some 1 else if a=22 then some 2 else none) := by
  fin_cases a
  all_goals first
    | exact RecoveryFocus.pick_slot _ RowOccurrenceClear.injective 0
    | exact RecoveryFocus.pick_slot _ RowOccurrenceClear.injective 1
    | exact RecoveryFocus.pick_slot _ RowOccurrenceClear.injective 2
    | decide

theorem cleared_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) (i j w C D : ℕ)
    (source : List Bool) (pos : ℕ) (positive negative : List Bool) :
    RowOccurrenceClear.tapes D (padded gs i j w C D source pos positive negative).tapes=
      (entry gs j w C D source pos positive negative).tapes := by
  funext a
  by_cases h19 : a=19
  · subst a; simp [RowOccurrenceClear.tapes,install,clear_pick,RowOccurrenceClear.output,
      entry,RowOccurrenceAppend.entry,RowOccurrenceAppend.blank,Composition.leftConfig,
      Composition.restart,ZeroPadding.config,caps,ZeroPadding.pad]
  have he := (RowOccurrenceAppend.ready_except_index gs i j w C D source pos positive negative a h19).2
  by_cases h21 : a=21
  · subst a
    have hh := (pad_index gs 0 j w C D source pos positive negative).2.2.2.2.1
    simpa [RowOccurrenceClear.tapes,install,clear_pick,RowOccurrenceClear.output,
      padded,entry,RowOccurrenceAppend.entry,RowOccurrenceAppend.blank,Composition.leftConfig,
      Composition.restart,ZeroPadding.config,caps] using hh.symm
  by_cases h22 : a=22
  · subst a
    have hh := (pad_index gs 0 j w C D source pos positive negative).2.2.2.2.2
    simpa [RowOccurrenceClear.tapes,install,clear_pick,RowOccurrenceClear.output,
      padded,entry,RowOccurrenceAppend.entry,RowOccurrenceAppend.blank,Composition.leftConfig,
      Composition.restart,ZeroPadding.config,caps] using hh.symm
  simpa [RowOccurrenceClear.tapes,install,clear_pick,padded,entry,RowOccurrenceAppend.entry,
    RowOccurrenceAppend.blank,Composition.leftConfig,Composition.restart,ZeroPadding.config,caps,
    h19,h21,h22,ZeroPadding.pad] using he

theorem reusable_run {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i<gs.length)
    (j : ℕ) (hj : j≤n) (w C D : ℕ) (pre tail positive negative : List Bool)
    (hC : RowPowerNativeReset.rawTime (RowCachedCoordinateAppend.value gs i hi j hj) w+1≤C)
    (hD : RowCachedCoordinateAppend.budget gs i hi j hj w C+1≤D) (hindex : i+2≤D) :
    let source := pre++RowIndexField.word i++tail
    let P := positive++marks (RowPowerNativeReusable.block w (RowCachedCoordinateAppend.value gs i hi j hj) false)
    let N := negative++marks (RowPowerNativeReusable.block w (RowCachedCoordinateAppend.value gs i hi j hj) true)
    ∃ r,runFrom machine (budget gs i hi j hj w C D)
      (entry gs j w C D source pre.length positive negative)=some r ∧
      r.final.heads=(entry gs j w C D source (pre.length+i+1) P N).heads ∧
      r.final.tapes=(entry gs j w C D source (pre.length+i+1) P N).tapes ∧
      r.steps=budget gs i hi j hj w C D := by
  dsimp only
  obtain ⟨raw,hr,rh,rt,rs⟩ := RowOccurrenceAppend.append_run gs i hi j hj w C D pre tail positive negative hC hD
  obtain ⟨called,hc,cf,cs,_⟩ := ZeroPadding.run_config RowOccurrenceAppend.machine (caps D) _ _ raw hr
  let result := padded gs i j w C D (pre++RowIndexField.word i++tail) (pre.length+i+1)
    (positive++marks (RowPowerNativeReusable.block w (RowCachedCoordinateAppend.value gs i hi j hj) false))
    (negative++marks (RowPowerNativeReusable.block w (RowCachedCoordinateAppend.value gs i hi j hj) true))
  have ch : called.final.heads=result.heads := by rw [cf]; exact rh
  have ct : called.final.tapes=result.tapes := by
    rw [cf]
    change (fun a=>ZeroPadding.pad (caps D a) (raw.final.tapes a))=_
    rw [rt]
    rfl
  obtain ⟨hi',hd,hl,ht,hd',hl'⟩ := pad_index gs i j w C D
    (pre++RowIndexField.word i++tail) (pre.length+i+1) _ _
  have hb : (result.tapes 19).length≤D := by
    rw [ht,ZeroPadding.pad_length,UnaryTemplate.tape_length]
    exact max_le le_rfl hindex
  obtain ⟨clear,hclear,clearH,clearT,clearS⟩ := RowOccurrenceClear.clear_run D called.final.heads called.final.tapes
    (ch ▸ hi') (ch ▸ hd) (ch ▸ hl) (ct ▸ hb) (ct ▸ hd') (ct ▸ hl')
  have whole := Composition.run_join RowOccurrenceAppend.machine RowOccurrenceClear.machine _ _ _ called clear hc hclear
  have time : RowOccurrenceAppend.budget gs i hi j hj w C D+1+(2*D+6)=budget gs i hi j hj w C D := by
    unfold budget
    omega
  rw [time] at whole
  refine ⟨Composition.joinedReceipt called clear,whole,?_,?_,?_⟩
  · change clear.final.heads=_
    rw [clearH,ch]
    exact cleared_heads gs i j w C D _ _ _ _
  · change clear.final.tapes=_
    rw [clearT,ct]
    exact cleared_tapes gs i j w C D _ _ _ _
  · change called.steps+1+clear.steps=_
    rw [cs,rs,clearS,time]

end NearCubicWires.RepairOrdinary.RowOccurrenceReusable
