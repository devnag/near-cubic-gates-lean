import Proof.Hierarchy.CompetitorResidueTableWorkspace

/-! Both operands are physically read from consecutive W-bit segments of
the one raw interleaved P/N stream. Neither operand is a prepared input. -/
namespace NearCubicWires.RepairOrdinary.CompetitorResidueTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def positiveProgram := CompetitorPlaneLoad.program (19 : Fin 27) 20 9 0 10
noncomputable def negativeProgram := CompetitorPlaneLoad.program (19 : Fin 27) 20 9 1 10
noncomputable def fieldsProgram := Composition.machine positiveProgram negativeProgram
noncomputable def firstLoaded (w a : ℕ) (ambient : Fin 27 → List Bool) :=
  Function.update (clean w ambient) 0 (ZeroPadding.pad (capacity w) (frame (binary w a)))
noncomputable def loaded (w a b : ℕ) (ambient : Fin 27 → List Bool) :=
  Function.update (firstLoaded w a ambient) 1 (ZeroPadding.pad (capacity w) (frame (binary w b)))

theorem fields_run (w q a b : ℕ) (pre suffix output : List Bool) (ambient : Fin 27 → List Bool)
    (h : Store w q (pre++CompetitorPlane.pairWord w a b++suffix) output ambient)
    (ha : a<2^w) (hb : b<2^w) :
    ∃ r,runFrom fieldsProgram (8*w+7)
      (cfg fieldsProgram.start pre.length output.length (clean w ambient))=some r ∧
      r.final.heads=heads (pre.length+2*w) output.length ∧
      r.final.tapes=loaded w a b ambient ∧ r.steps=8*w+7 := by
  have hcap : 2*w+1≤capacity w := by unfold capacity CompetitorReusableDecision.capacity; nlinarith
  have hc19 := (clean_keep w ambient 19 (by simp)).trans h.source
  have hc20 := (clean_keep w ambient 20 (by simp)).trans h.widthCopy
  have hc9 := (clean_keep w ambient 9 (by simp)).trans h.width
  have hc0 := clean_work w ambient 0
  have hc1 := clean_work w ambient 1
  have hc10 := clean_work w ambient 7
  obtain ⟨first,hfirst,hfh,hft,hfs⟩ := CompetitorPlaneLoad.field_run (19 : Fin 27) 20 9 0 10
    (by decide) pre (binary w b++suffix) w w a 0 (capacity w)
    (heads pre.length output.length) (clean w ambient) (by omega) ha hcap rfl rfl rfl rfl rfl
    (by simpa [CompetitorPlane.pairWord,List.append_assoc] using hc19)
    (by simpa using hc20) hc9 hc0 hc10
  have hh : Function.update (heads pre.length output.length) 19 (pre.length+w)=
      heads (pre.length+w) output.length := by
    funext i
    by_cases hi : i=19 <;> simp [heads,hi]
  rw [hh] at hfh
  have hsource : firstLoaded w a ambient 19=(pre++binary w a)++binary w b++suffix := by
    simp only [firstLoaded,Function.update_of_ne (by decide : (19 : Fin 27)≠0)]
    simpa [CompetitorPlane.pairWord,List.append_assoc] using hc19
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := CompetitorPlaneLoad.field_run (19 : Fin 27) 20 9 1 10
    (by decide) (pre++binary w a) suffix w w b 0 (capacity w)
    (heads (pre.length+w) output.length) (firstLoaded w a ambient) (by omega) hb hcap
    (by simp [heads]) rfl rfl rfl rfl hsource
    (by simpa [firstLoaded] using hc20) (by simpa [firstLoaded] using hc9)
    (by simpa [firstLoaded,workSlots] using hc1) (by simpa [firstLoaded,workSlots] using hc10)
  have he : Composition.restart first.final negativeProgram.start=
      cfg negativeProgram.start (pre.length+w) output.length (firstLoaded w a ambient) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hl' : runFrom negativeProgram (4*w+3) (Composition.restart first.final negativeProgram.start)=some last := by
    rw [he]
    exact hlast
  have hall := Composition.run_join positiveProgram negativeProgram _ _ _ first last hfirst hl'
  have htime : (4*w+3)+1+(4*w+3)=8*w+7 := by omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt first last,hall,?_,hlt,?_⟩
  · change last.final.heads=_
    rw [hlh]
    funext i
    by_cases hi : i=19 <;> simp [heads,hi]
    omega
  · change first.steps+1+last.steps=8*w+7
    omega

end NearCubicWires.RepairOrdinary.CompetitorResidueTable
