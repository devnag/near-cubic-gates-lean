import Proof.Hierarchy.CompetitorValidityRecord

/-! One complete reusable validity-list iteration: erase bounded scratch,
read six fields at the global stream cursor, and execute the exact signed
rational comparison. Its whole endpoint is suitable for the next iteration. -/
namespace NearCubicWires.RepairOrdinary.CompetitorValidity
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Store (b : ℕ) (source : List Bool) (tapes : Fin 71 → List Bool) : Prop where
  width : tapes 6=List.replicate (CompetitorRationalDecision.width b) true
  source : tapes 67=source
  driver : tapes 69=List.replicate (capacity b) true
  reset : tapes 70=List.replicate (capacity b+1) false
  scratch : ∀ j,(tapes (scratchSlot j)).length≤capacity b

theorem store_data (b : ℕ) (source : List Bool) (tapes : Fin 71 → List Bool) (h : Store b source tapes) :
    data b source (fun j => tapes (scratchSlot j))=tapes := by
  funext i
  fin_cases i
  all_goals first | exact h.width.symm | exact h.source.symm | exact h.driver.symm | exact h.reset.symm | rfl

theorem native_other (i : Fin 71) (hi : 67 ≤ i.val) : ∀ j,nativeSlots j≠i := by
  intro j h
  have hv := congrArg Fin.val h
  change j.val=i.val at hv
  omega

theorem native_store (b : ℕ) (source : List Bool) (a : Comparison) (out : Fin 67 → List Bool)
    (hb : ∀ i,(out i).length≤capacity b) (hw : out 6=List.replicate (width b) true) :
    Store b source (install nativeSlots (loadedRecord b source a) out) := by
  constructor
  · exact (install_slot nativeSlots native_injective _ _ 6).trans hw
  · exact (install_other nativeSlots _ _ 67 (native_other _ (by decide))).trans
      (record_other b source a 67 (by decide))
  · exact (install_other nativeSlots _ _ 69 (native_other _ (by decide))).trans
      (record_other b source a 69 (by decide))
  · exact (install_other nativeSlots _ _ 70 (native_other _ (by decide))).trans
      (record_other b source a 70 (by decide))
  · intro j
    by_cases hj : j.val<66
    · have hsmall : (scratchSlot j).val<67 := by
        unfold scratchSlot
        split_ifs <;> simp only <;> omega
      let i : Fin 67 := ⟨(scratchSlot j).val,hsmall⟩
      have he : nativeSlots i=scratchSlot j := Fin.ext rfl
      rw [← he,install_slot nativeSlots native_injective]
      exact hb i
    · have hj' : j=66 := Fin.ext (by omega)
      subst j
      change (install nativeSlots (loadedRecord b source a) out 68).length≤capacity b
      rw [install_other nativeSlots _ _ 68 (native_other _ (by decide)),record_other b source a 68 (by decide)]
      simp [erased,data]

noncomputable def recordTail := Composition.machine (fieldsProgram targets) nativeProgram
noncomputable def recordProgram := Composition.machine eraseProgram recordTail
def recordBudget (b : ℕ) := 11000*(b+1)^2

theorem record_run (b : ℕ) (a : Comparison) (pre suffix : List Bool) (ambient : Fin 71 → List Bool)
    (ha : a.Valid b) (hstore : Store b (pre++a.word b++suffix) ambient) :
    ∃ r,runFrom recordProgram (recordBudget b) (cfg recordProgram.start pre.length ambient)=some r ∧
      r.final.heads=heads (pre.length+20*b+22) ∧
      Store b (pre++a.word b++suffix) r.final.tapes ∧
      (readTapeBit (r.final.tapes 65) 0=true ↔ a.passes) ∧ r.steps≤recordBudget b := by
  let source := pre++a.word b++suffix
  let pos := pre.length+20*b+22
  obtain ⟨er,her,herh,hert,hers⟩ := erase_run b source pre.length (fun j => ambient (scratchSlot j)) hstore.scratch
  rw [store_data b source ambient hstore] at her
  obtain ⟨fields,hfields,hfieldh,hfieldt,hfieldsizes⟩ := record_fields_run b a pre suffix
  obtain ⟨out,hout,hbounds,hwidth,hflag⟩ := padded_decision_run b a.nums a.leftDenominator a.rightDenominator
    ha.nums ha.left ha.right ha.leftPositive ha.rightPositive
  have hh : ∀ j,heads pos (nativeSlots j)=0 := by
    intro j
    have hj : (nativeSlots j).val≠67 := by change j.val≠67; omega
    simp [heads,hj]
  obtain ⟨native,hnative,hnh,hnt,hns⟩ := bounded_focused_run nativeSlots native_injective _ _ _ hout
    (heads pos) (loadedRecord b source a) hh (record_native b source a)
  have heNative : Composition.restart fields.final nativeProgram.start=
      cfg nativeProgram.start pos (loadedRecord b source a) := by
    apply configuration_ext
    · rfl
    · exact hfieldh
    · exact hfieldt
  have hn' : runFrom nativeProgram (2000*(b+1)^2)
      (Composition.restart fields.final nativeProgram.start)=some native := by
    rw [heNative]
    exact hnative
  have htail := Composition.run_join (fieldsProgram targets) nativeProgram (40*b+56)
    (2000*(b+1)^2) _ fields native hfields hn'
  let tail := Composition.joinedReceipt fields native
  have heFields : Composition.restart er.final recordTail.start=
      Composition.leftConfig _ (cfg (fieldsProgram targets).start pre.length (erased b source)) := by
    apply configuration_ext
    · rfl
    · exact herh
    · exact hert
  have ht' : runFrom recordTail ((40*b+56)+1+2000*(b+1)^2)
      (Composition.restart er.final recordTail.start)=some tail := by
    rw [heFields]
    exact htail
  have hall := Composition.run_join eraseProgram recordTail (2*capacity b+4)
    ((40*b+56)+1+2000*(b+1)^2) _ er tail her ht'
  let r := Composition.joinedReceipt er tail
  have hcost : (2*capacity b+4)+1+((40*b+56)+1+2000*(b+1)^2)≤recordBudget b := by
    unfold capacity recordBudget
    nlinarith
  have hmore := runFrom_moreFuel recordProgram _
    (recordBudget b-((2*capacity b+4)+1+((40*b+56)+1+2000*(b+1)^2))) _ r hall
  rw [Nat.add_sub_of_le hcost] at hmore
  refine ⟨r,hmore,hnh,?_,?_,?_⟩
  · change Store b source native.final.tapes
    rw [hnt]
    exact native_store b source a out hbounds hwidth
  · change readTapeBit (native.final.tapes 65) 0=true ↔ a.passes
    have h65 : install nativeSlots (loadedRecord b source a) out 65=out 65 :=
      install_slot nativeSlots native_injective _ _ 65
    rw [hnt,h65]
    exact hflag
  · change er.steps+1+(fields.steps+1+native.steps)≤recordBudget b
    omega

end NearCubicWires.RepairOrdinary.CompetitorValidity
