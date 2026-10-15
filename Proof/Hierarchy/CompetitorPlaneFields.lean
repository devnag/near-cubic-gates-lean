import Proof.Hierarchy.CompetitorPlanePrepare

/-! Three paid input fields for one aligned signed-plane update: the native
matrix count and the previous raw positive/negative accumulator pair. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlaneStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def countProgram := CompetitorPlaneLoad.program (18 : Fin 27) 20 9 8 23
noncomputable def positiveProgram := CompetitorPlaneLoad.program (19 : Fin 27) 24 9 14 23
noncomputable def negativeProgram := CompetitorPlaneLoad.program (19 : Fin 27) 24 9 15 23
noncomputable def oldProgram := Composition.machine positiveProgram negativeProgram
noncomputable def fieldsProgram := Composition.machine countProgram oldProgram
def loadField (w : ℕ) (target : Fin 27) (count : ℕ) (ambient : Fin 27 → List Bool) :=
  Function.update ambient target (ZeroPadding.pad (CompetitorPlane.capacity w) (frame (binary w count)))
noncomputable def loadedFields (w count positive negative : ℕ) (ambient : Fin 27 → List Bool) :=
  loadField w 15 negative (loadField w 14 positive (loadField w 8 count (widthPrepared w ambient)))

theorem width_keep (w : ℕ) (ambient : Fin 27 → List Bool) (i : Fin 27) (hi : retainedSlot i) :
    widthPrepared w ambient i=ambient i := by
  have h24 : i≠24 := by rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  rw [widthPrepared,Function.update_of_ne h24]
  exact clean_keep w ambient i hi
theorem width_work (w : ℕ) (ambient : Fin 27 → List Bool) (i : Fin 27) (hi : working i) (h24 : i≠24) :
    widthPrepared w ambient i=List.replicate (CompetitorPlane.capacity w) false := by
  rw [widthPrepared,Function.update_of_ne h24]
  exact clean_work w ambient i hi

theorem fields_run (b w count positive negative : ℕ) (bits preCount tailCount preOld tailOld output : List Bool)
    (ambient : Fin 27 → List Bool)
    (h : Store b w bits (preCount++binary b count++tailCount)
      (preOld++CompetitorPlane.pairWord w positive negative++tailOld) output ambient)
    (hb : b≤w) (hc : count<2^b) (hp : positive<2^w) (hn : negative<2^w) :
    ∃ r,runFrom fieldsProgram (12*w+11)
        (cfg fieldsProgram.start preCount.length preOld.length output.length (widthPrepared w ambient))=some r ∧
      r.steps=12*w+11 ∧ r.final.heads=heads (preCount.length+b) (preOld.length+2*w) output.length ∧
      r.final.tapes=loadedFields w count positive negative ambient := by
  have hcap : 2*w+1≤CompetitorPlane.capacity w := by unfold CompetitorPlane.capacity; nlinarith
  let middle := widthPrepared w ambient
  have hm9 : middle 9=List.replicate w true := (width_keep w ambient 9 (by simp [retainedSlot])).trans h.width
  have hm18 : middle 18=preCount++binary b count++tailCount := (width_keep w ambient 18 (by simp [retainedSlot])).trans h.counts
  have hm19 : middle 19=preOld++binary w positive++binary w negative++tailOld := by
    simpa only [CompetitorPlane.pairWord,List.append_assoc] using (width_keep w ambient 19 (by simp [retainedSlot])).trans h.old
  have hm20 : middle 20=ZeroPadding.pad 0 (List.replicate b true) := by
    simpa only [ZeroPadding.pad_zero] using (width_keep w ambient 20 (by simp [retainedSlot])).trans h.nativeWidth
  have hm24 : middle 24=ZeroPadding.pad (CompetitorPlane.capacity w) (List.replicate w true) := Function.update_self ..
  have hm8 : middle 8=List.replicate (CompetitorPlane.capacity w) false := width_work w ambient 8 (by simp [working]) (by decide)
  have hm14 : middle 14=List.replicate (CompetitorPlane.capacity w) false := width_work w ambient 14 (by simp [working]) (by decide)
  have hm15 : middle 15=List.replicate (CompetitorPlane.capacity w) false := width_work w ambient 15 (by simp [working]) (by decide)
  have hm23 : middle 23=List.replicate (CompetitorPlane.capacity w) false := width_work w ambient 23 (by simp [working]) (by decide)
  obtain ⟨c,hrc,hch,hct,hcs⟩ := CompetitorPlaneLoad.field_run (18 : Fin 27) 20 9 8 23 (by decide)
    preCount tailCount b w count 0 (CompetitorPlane.capacity w)
    (heads preCount.length preOld.length output.length) middle hb hc hcap rfl rfl rfl rfl rfl hm18 hm20 hm9 hm8 hm23
  let afterCount := loadField w 8 count middle
  have hch' : c.final.heads=heads (preCount.length+b) preOld.length output.length := by
    rw [hch]
    funext i
    by_cases hi : i=18
    · subst i; simp [heads]
    · have hv : i.val≠18 := fun hh => hi (Fin.ext hh)
      simp [Function.update_of_ne hi,heads,hv]
  obtain ⟨p,hrp,hph,hpt,hps⟩ := CompetitorPlaneLoad.field_run (19 : Fin 27) 24 9 14 23 (by decide)
    preOld (binary w negative++tailOld) w w positive (CompetitorPlane.capacity w) (CompetitorPlane.capacity w)
    (heads (preCount.length+b) preOld.length output.length) afterCount (by rfl) hp hcap rfl rfl rfl rfl rfl
    (by simpa [afterCount,loadField,List.append_assoc] using hm19)
    (by simpa [afterCount,loadField] using hm24) (by simpa [afterCount,loadField] using hm9)
    (by simpa [afterCount,loadField] using hm14) (by simpa [afterCount,loadField] using hm23)
  let afterPositive := loadField w 14 positive afterCount
  have hph' : p.final.heads=heads (preCount.length+b) (preOld.length+w) output.length := by
    rw [hph]
    funext i
    by_cases hi : i=19
    · subst i; simp [heads]
    · have hv : i.val≠19 := fun hh => hi (Fin.ext hh)
      simp [Function.update_of_ne hi,heads,hv]
  obtain ⟨n,hrn,hnh,hnt,hns⟩ := CompetitorPlaneLoad.field_run (19 : Fin 27) 24 9 15 23 (by decide)
    (preOld++binary w positive) tailOld w w negative (CompetitorPlane.capacity w) (CompetitorPlane.capacity w)
    (heads (preCount.length+b) (preOld.length+w) output.length) afterPositive (by rfl) hn hcap
    (by simp [heads]) rfl rfl rfl rfl
    (by simpa [afterPositive,afterCount,loadField] using hm19)
    (by simpa [afterPositive,afterCount,loadField] using hm24)
    (by simpa [afterPositive,afterCount,loadField] using hm9)
    (by simpa [afterPositive,afterCount,loadField] using hm15)
    (by simpa [afterPositive,afterCount,loadField] using hm23)
  have hnrestart : Composition.restart p.final negativeProgram.start=
      RecoveryCalls.restarted negativeProgram (heads (preCount.length+b) (preOld.length+w) output.length) afterPositive := by
    apply configuration_ext
    · rfl
    · exact hph'
    · exact hpt
  have hnrun : runFrom negativeProgram (4*w+3) (Composition.restart p.final negativeProgram.start)=some n := by
    rw [hnrestart]
    exact hrn
  have hpRun : runFrom positiveProgram (4*w+3)
      (RecoveryCalls.restarted positiveProgram (heads (preCount.length+b) preOld.length output.length) afterCount)=some p := hrp
  have hold := Composition.run_join positiveProgram negativeProgram _ _ _ p n hpRun hnrun
  let oldRun := Composition.joinedReceipt p n
  have hcrestart : Composition.restart c.final oldProgram.start=
      Composition.leftConfig 4 (RecoveryCalls.restarted positiveProgram (heads (preCount.length+b) preOld.length output.length) afterCount) := by
    apply configuration_ext
    · rfl
    · exact hch'
    · exact hct
  have holdRun : runFrom oldProgram ((4*w+3)+1+(4*w+3)) (Composition.restart c.final oldProgram.start)=some oldRun := by
    rw [hcrestart]
    exact hold
  have hall := Composition.run_join countProgram oldProgram _ _ _ c oldRun hrc holdRun
  have htime : (4*w+3)+1+((4*w+3)+1+(4*w+3))=12*w+11 := by omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt c oldRun,hall,?_,?_,hnt⟩
  · change c.steps+1+(p.steps+1+n.steps)=12*w+11
    omega
  · change n.final.heads=heads (preCount.length+b) (preOld.length+2*w) output.length
    rw [hnh]
    funext i
    by_cases hi : i=19
    · subst i; simp [heads]; omega
    · have hv : i.val≠19 := fun hh => hi (Fin.ext hh)
      simp [Function.update_of_ne hi,heads,hv]

end NearCubicWires.RepairOrdinary.CompetitorPlaneStream
