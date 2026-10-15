import Proof.Hierarchy.CompetitorBankMergeKernel

/-! Each addend is physically loaded from its own aligned raw bank. Only
the selected source cursor advances; the shared W and local reset are paid. -/
namespace NearCubicWires.RepairOrdinary.CompetitorBankMerge
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def leftProgram := CompetitorPlaneLoad.program (19 : Fin 27) 20 9 0 10
noncomputable def rightProgram := CompetitorPlaneLoad.program (23 : Fin 27) 20 9 1 10
noncomputable def fieldsProgram := Composition.machine leftProgram rightProgram
noncomputable def leftLoaded (w a : ℕ) (ambient : Fin 27 → List Bool) :=
  Function.update (clean w ambient) 0 (ZeroPadding.pad (capacity w) (frame (binary w a)))
noncomputable def loaded (w a b : ℕ) (ambient : Fin 27 → List Bool) :=
  Function.update (leftLoaded w a ambient) 1 (ZeroPadding.pad (capacity w) (frame (binary w b)))

theorem loaded_stored (w a b : ℕ) (left right out : List Bool) (ambient : Fin 27 → List Bool)
    (h : Store w left right out ambient) : Store w left right out (loaded w a b ambient) := by
  have ha : (ZeroPadding.pad (capacity w) (frame (binary w a))).length≤capacity w := by
    simp only [ZeroPadding.pad_length,frame_length,binary_length]
    exact max_le le_rfl (word_fits w)
  have hb : (ZeroPadding.pad (capacity w) (frame (binary w b))).length≤capacity w := by
    simp only [ZeroPadding.pad_length,frame_length,binary_length]
    exact max_le le_rfl (word_fits w)
  exact ((h.clean).work_update 0 _ ha).work_update 1 _ hb

theorem loaded_input (w a b : ℕ) (ambient : Fin 27 → List Bool) (i : Fin 4) :
    loaded w a b ambient (addSlots i)=addInput w a b i := by
  have h2 := CompetitorResidueTable.clean_work w ambient 2
  have h3 := CompetitorResidueTable.clean_work w ambient 3
  change clean w ambient 2=List.replicate (capacity w) false at h2
  change clean w ambient 3=List.replicate (capacity w) false at h3
  fin_cases i <;> simp [loaded,leftLoaded,addSlots,addInput,h2,h3]

theorem fields_run (w a b : ℕ) (preA suffixA preB suffixB out : List Bool) (ambient : Fin 27 → List Bool)
    (h : Store w (preA++binary w a++suffixA) (preB++binary w b++suffixB) out ambient)
    (hfit : a+b<2^w) :
    ∃ r,runFrom fieldsProgram (8*w+7)
      (cfg fieldsProgram.start preA.length preB.length out.length (clean w ambient))=some r ∧
      r.final.heads=heads (preA.length+w) (preB.length+w) out.length ∧
      r.final.tapes=loaded w a b ambient ∧ r.steps=8*w+7 := by
  have hclean := h.clean
  have h0 := CompetitorResidueTable.clean_work w ambient 0
  have h1 := CompetitorResidueTable.clean_work w ambient 1
  have h10 := CompetitorResidueTable.clean_work w ambient 7
  obtain ⟨first,hfirst,hfh,hft,hfs⟩ := CompetitorPlaneLoad.field_run (19 : Fin 27) 20 9 0 10
    (by decide) preA suffixA w w a 0 (capacity w) (heads preA.length preB.length out.length) (clean w ambient)
    le_rfl (by omega) (word_fits w) rfl rfl rfl rfl rfl hclean.sourceLeft
    (by simpa using hclean.widthCopy) hclean.width h0 h10
  have hh : Function.update (heads preA.length preB.length out.length) 19 (preA.length+w)=
      heads (preA.length+w) preB.length out.length := by
    funext i
    by_cases hi : i=19 <;> simp [heads,hi]
  rw [hh] at hfh
  have hleft : Store w (preA++binary w a++suffixA) (preB++binary w b++suffixB) out (leftLoaded w a ambient) := by
    apply hclean.work_update 0
    simp only [ZeroPadding.pad_length,frame_length,binary_length]
    exact max_le le_rfl (word_fits w)
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := CompetitorPlaneLoad.field_run (23 : Fin 27) 20 9 1 10
    (by decide) preB suffixB w w b 0 (capacity w) (heads (preA.length+w) preB.length out.length) (leftLoaded w a ambient)
    le_rfl (by omega) (word_fits w) rfl rfl rfl rfl rfl hleft.sourceRight
    (by simpa using hleft.widthCopy) hleft.width
    (by simpa [leftLoaded,workSlots,CompetitorResidueTable.workSlots] using h1)
    (by simpa [leftLoaded,workSlots,CompetitorResidueTable.workSlots] using h10)
  have he : Composition.restart first.final rightProgram.start=
      cfg rightProgram.start (preA.length+w) preB.length out.length (leftLoaded w a ambient) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hl' : runFrom rightProgram (4*w+3) (Composition.restart first.final rightProgram.start)=some last := by
    rw [he]
    exact hlast
  have hall := Composition.run_join leftProgram rightProgram _ _ _ first last hfirst hl'
  have htime : (4*w+3)+1+(4*w+3)=8*w+7 := by omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt first last,hall,?_,hlt,?_⟩
  · change last.final.heads=_
    rw [hlh]
    funext i
    by_cases hi : i=23 <;> simp [heads,hi]
  · change first.steps+1+last.steps=8*w+7
    omega

end NearCubicWires.RepairOrdinary.CompetitorBankMerge
