import Proof.MachineModel.UDecoderRun

/-! The decoder's finite focus leaves the input/witness scalar suppliers
untouched. This supplies the next physical witness and initialization entry. -/
namespace NearCubicWires.RepairOrdinary.UDecoder
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem slots_outside (i : Fin 50) (h6 : i≠6) (h48 : i≠48) :
    ∀ j,slots j≠i.castAdd 19 := by
  intro j hj
  have hv := congrArg Fin.val hj
  have hi := i.isLt
  have hn6 : i.val≠6 := by intro h; exact h6 (Fin.ext h)
  have hn48 : i.val≠48 := by intro h; exact h48 (Fin.ext h)
  fin_cases j <;> simp [slots] at hv <;> omega

theorem focus_retained {s u : ℕ} (base : Configuration 50 s) (small : Configuration 21 u)
    (i : Fin 50) (h6 : i≠6) (h48 : i≠48) :
    (RecoveryFocus.config slots (extended base).heads (extended base).tapes small).heads (i.castAdd 19)=base.heads i ∧
    (RecoveryFocus.config slots (extended base).heads (extended base).tapes small).tapes (i.castAdd 19)=base.tapes i := by
  have hnone : RecoveryFocus.pick slots (i.castAdd 19)=none := by
    have hn : ¬∃j,slots j=i.castAdd 19 := by simpa using slots_outside i h6 h48
    simp [RecoveryFocus.pick,hn]
  simp [RecoveryFocus.config,hnone,extended,TapeEmbedding.config]

def FieldSuppliers (raw witness : List Bool) (heads : Fin 69 → ℕ) (tapes : Fin 69 → List Bool) : Prop :=
  ∃ code x bound padding,
    raw=VerifierInputFields.source code x bound padding ∧ UInputScalars.Guards raw x bound ∧
    tapes 0=frame raw ∧ tapes 1=frame witness ∧ tapes 8=frame x ∧
    tapes 20=List.replicate (ClockDyadicLedger.width raw.length) true ∧
    tapes 21=List.replicate (2*ClockDyadicLedger.width raw.length) true ∧
    tapes 22=List.replicate (2*ClockDyadicLedger.width raw.length+2) true ∧
    tapes 26=frame (SignedSortKey.binary (ClockDyadicLedger.width raw.length) (RadixSemantics.value bound)) ∧
    heads 1=0 ∧ heads 8=0 ∧ heads 20=0 ∧ heads 21=0 ∧ heads 22=0 ∧ heads 26=0

theorem successful_fields (raw witness : List Bool)
    (final : Configuration 69 (Fintype.card (RecoveryCalls.Control sizes)))
    (h : Successful raw witness final) : FieldSuppliers raw witness final.heads final.tapes := by
  obtain ⟨code,x,bound,padding,base,small,he,hg,hprep,hh,hwit,_,hfheads,hftapes,_⟩ := h
  obtain ⟨code',x',bound',padding',he',hg',h0,_,hx,_,_,hw,hI,hK,hB,_,_⟩ := hprep
  obtain ⟨rfl,rfl,rfl,rfl⟩ := UInputEntry.source_unique _ _ _ _ _ _ _ _ (he.symm.trans he')
  have ht (i : Fin 50) (h6 : i≠6) (h48 : i≠48) :
      final.heads (i.castAdd 19)=base.heads i ∧ final.tapes (i.castAdd 19)=base.tapes i := by
    rw [hfheads,hftapes]
    exact focus_retained base small i h6 h48
  refine ⟨code,x,bound,padding,he,hg,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (ht 0 (by decide) (by decide)).2.trans h0
  · exact (ht 1 (by decide) (by decide)).2.trans hwit
  · exact (ht 8 (by decide) (by decide)).2.trans hx
  · exact (ht 20 (by decide) (by decide)).2.trans hw
  · exact (ht 21 (by decide) (by decide)).2.trans hI
  · exact (ht 22 (by decide) (by decide)).2.trans hK
  · exact (ht 26 (by decide) (by decide)).2.trans hB
  · simpa [hh,UInputOrdinary.heads] using (ht 1 (by decide) (by decide)).1
  · simpa [hh,UInputOrdinary.heads] using (ht 8 (by decide) (by decide)).1
  · simpa [hh,UInputOrdinary.heads] using (ht 20 (by decide) (by decide)).1
  · simpa [hh,UInputOrdinary.heads] using (ht 21 (by decide) (by decide)).1
  · simpa [hh,UInputOrdinary.heads] using (ht 22 (by decide) (by decide)).1
  · simpa [hh,UInputOrdinary.heads] using (ht 26 (by decide) (by decide)).1

end NearCubicWires.RepairOrdinary.UDecoder
