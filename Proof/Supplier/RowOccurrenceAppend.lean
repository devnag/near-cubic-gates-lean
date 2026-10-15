import Proof.Supplier.RowIndexField

/-! A physical ordered index field selects a coordinate from the retained
child cache and appends its signed radix block. The stream remains at the
next occurrence, including when adjacent indices are equal. -/
namespace NearCubicWires.RepairOrdinary.RowOccurrenceAppend
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 2 → Fin 24 := ![23,19]
theorem injective : Function.Injective slots := by decide
noncomputable def first := RecoveryFocus.machine slots RowIndexField.machine
noncomputable def last := TapeEmbedding.machine 1 RowCachedCoordinateReusable.machine
noncomputable def machine := Composition.machine first last
noncomputable def ready {n : ℕ} (gs : List (ExactThresholdGate n)) (i j w C D : ℕ)
    (source : List Bool) (pos : ℕ) (positive negative : List Bool) :=
  TapeEmbedding.config (fun _ : Fin 1=>pos) (fun _=>source)
    (RowCachedCoordinateReusable.entry gs i j w C D positive negative)
noncomputable def blank {n : ℕ} (gs : List (ExactThresholdGate n)) (j w C D : ℕ)
    (source : List Bool) (pos : ℕ) (positive negative : List Bool) :=
  let a := ready gs 0 j w C D source pos positive negative
  (⟨a.control,Function.update a.heads 19 0,Function.update a.tapes 19 []⟩ : Configuration 24 _)
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) (j w C D : ℕ)
    (source : List Bool) (pos : ℕ) (positive negative : List Bool) :=
  Composition.restart (blank gs j w C D source pos positive negative) machine.start
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i<gs.length)
    (j : ℕ) (hj : j≤n) (w C D : ℕ) :=
  2*i+4+RowCachedCoordinateReusable.budget gs i hi j hj w C D

theorem ready_except_index {n : ℕ} (gs : List (ExactThresholdGate n)) (i j w C D : ℕ)
    (source : List Bool) (pos : ℕ) (positive negative : List Bool) (a : Fin 24) (ha : a≠19) :
    (ready gs i j w C D source pos positive negative).heads a=
      (ready gs 0 j w C D source pos positive negative).heads a ∧
    (ready gs i j w C D source pos positive negative).tapes a=
      (ready gs 0 j w C D source pos positive negative).tapes a := by
  simp only [ready,RowCachedCoordinateReusable.entry,
    RowCachedCoordinateReusable.extended,Composition.leftConfig,TapeEmbedding.config,
    RowCachedCoordinateReset.entry,ZeroPadding.config,Rewind.recording,Rewind.config,
    RowCachedCoordinateAppend.entry,RowCachedCoordinateAppend.ready,
    RowCachedCoordinateAppend.extra,RowNativeCoordinateAppend.ready]
  fin_cases a <;> simp_all [Fin.addCases]

theorem pick (a : Fin 24) : RecoveryFocus.pick slots a=
    (if a=23 then some 0 else if a=19 then some 1 else none) := by
  fin_cases a
  all_goals first
    | exact RecoveryFocus.pick_slot slots injective 0
    | exact RecoveryFocus.pick_slot slots injective 1
    | decide

theorem append_run {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i<gs.length)
    (j : ℕ) (hj : j≤n) (w C D : ℕ) (pre tail positive negative : List Bool)
    (hC : RowPowerNativeReset.rawTime (RowCachedCoordinateAppend.value gs i hi j hj) w+1≤C)
    (hD : RowCachedCoordinateAppend.budget gs i hi j hj w C+1≤D) :
    let source := pre++RowIndexField.word i++tail
    let P := positive++marks (RowPowerNativeReusable.block w (RowCachedCoordinateAppend.value gs i hi j hj) false)
    let N := negative++marks (RowPowerNativeReusable.block w (RowCachedCoordinateAppend.value gs i hi j hj) true)
    ∃ r,runFrom machine (budget gs i hi j hj w C D)
      (entry gs j w C D source pre.length positive negative)=some r ∧
      r.final.heads=(ready gs i j w C D source (pre.length+i+1) P N).heads ∧
      r.final.tapes=(ready gs i j w C D source (pre.length+i+1) P N).tapes ∧
      r.steps=budget gs i hi j hj w C D := by
  dsimp only
  let source := pre++RowIndexField.word i++tail
  let before := blank gs j w C D source pre.length positive negative
  let parsed := ready gs i j w C D source (pre.length+i+1) positive negative
  obtain ⟨read,hr,rf,rs⟩ := RowIndexField.field_run pre tail i
  obtain ⟨scan,hs,sf,ss⟩ := RecoveryFocus.run_config slots injective RowIndexField.machine
    before.heads before.tapes _ _ read hr
  have hin : RecoveryFocus.config slots before.heads before.tapes
      (RowIndexField.entry source pre.length)=Composition.restart before first.start := by
    apply WilliamsSourceCrop.focus_same
    · intro a; fin_cases a <;> simp [before,blank,slots,ready,TapeEmbedding.config,Fin.addCases,RowIndexField.entry]
    · intro a; fin_cases a <;> simp [before,blank,slots,ready,TapeEmbedding.config,Fin.addCases,RowIndexField.entry]
  rw [hin] at hs
  have sh : scan.final.heads=parsed.heads := by
    rw [sf,rf]
    funext a
    by_cases h23 : a=23
    · subst a; simp [RecoveryFocus.config,pick,RowIndexField.back,parsed,ready,TapeEmbedding.config,Fin.addCases]
    by_cases h19 : a=19
    · subst a; simp [RecoveryFocus.config,pick,RowIndexField.back,parsed,ready,
        RowCachedCoordinateReusable.entry,RowCachedCoordinateReusable.extended,
        Composition.leftConfig,TapeEmbedding.config,RowCachedCoordinateReset.entry,
        ZeroPadding.config,Rewind.recording,Rewind.config,RowCachedCoordinateAppend.entry,
        RowCachedCoordinateAppend.ready,Fin.addCases]
    have he := (ready_except_index gs i j w C D source (pre.length+i+1) positive negative a h19).1
    have hp : (ready gs 0 j w C D source pre.length positive negative).heads a=
        (ready gs 0 j w C D source (pre.length+i+1) positive negative).heads a := by
      fin_cases a <;> first | contradiction | rfl
    simpa [RecoveryFocus.config,pick,h23,h19,before,blank,parsed] using hp.trans he.symm
  have st : scan.final.tapes=parsed.tapes := by
    rw [sf,rf]
    funext a
    by_cases h23 : a=23
    · subst a; simp [RecoveryFocus.config,pick,RowIndexField.back,parsed,ready,TapeEmbedding.config,Fin.addCases,source]
    by_cases h19 : a=19
    · subst a; simp [RecoveryFocus.config,pick,RowIndexField.back,parsed,ready,
        RowCachedCoordinateReusable.entry,RowCachedCoordinateReusable.extended,
        Composition.leftConfig,TapeEmbedding.config,RowCachedCoordinateReset.entry,
        ZeroPadding.config,Rewind.recording,Rewind.config,RowCachedCoordinateAppend.entry,
        RowCachedCoordinateAppend.ready,RowCachedCoordinateAppend.extra,Fin.addCases,ZeroPadding.pad,
        RowCachedCoordinateReset.caps]
    have he := (ready_except_index gs i j w C D source (pre.length+i+1) positive negative a h19).2
    have hp : (ready gs 0 j w C D source pre.length positive negative).tapes a=
        (ready gs 0 j w C D source (pre.length+i+1) positive negative).tapes a := by rfl
    simpa [RecoveryFocus.config,pick,h23,h19,before,blank,parsed] using hp.trans he.symm
  obtain ⟨row,hrow,rh,rt,rsteps⟩ := RowCachedCoordinateReusable.reusable_run gs i hi j hj positive negative w C D hC hD
  let rowRun := TapeEmbedding.receipt (fun _ : Fin 1=>pre.length+i+1) (fun _=>source) row
  have hlast := TapeEmbedding.run_embed RowCachedCoordinateReusable.machine
    (fun _ : Fin 1=>pre.length+i+1) (fun _=>source) _ _ row hrow
  have he : parsed=Composition.restart scan.final last.start := by
    apply configuration_ext
    · rfl
    · exact sh.symm
    · exact st.symm
  change runFrom last _ parsed=some rowRun at hlast
  rw [he] at hlast
  have whole := Composition.run_join first last _ _ _ scan rowRun hs hlast
  refine ⟨Composition.joinedReceipt scan rowRun,whole,?_,?_,?_⟩
  · dsimp only [Composition.joinedReceipt,Composition.rightConfig,rowRun,TapeEmbedding.receipt,TapeEmbedding.config]
    rw [rh]
    rfl
  · dsimp only [Composition.joinedReceipt,Composition.rightConfig,rowRun,TapeEmbedding.receipt,TapeEmbedding.config]
    rw [rt]
    rfl
  · change scan.steps+1+row.steps=_
    rw [ss,rs,rsteps]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.RowOccurrenceAppend
