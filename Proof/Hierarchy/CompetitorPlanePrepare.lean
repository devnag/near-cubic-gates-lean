import Proof.Hierarchy.CompetitorPlaneClear
import Proof.Hierarchy.CompetitorUnaryWidthCopy

/-! The enclosing plane-cell preparation begins with three independent
stream cursors, retained factor/widths and bounded local scratch. It clears
only scratch and physically duplicates the runtime accumulator width. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlaneStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open CompetitorPlaneWorkspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (countPos oldPos outputPos : ℕ) : Fin 27 → ℕ := fun i =>
  if i.val=17 then outputPos else if i.val=18 then countPos else if i.val=19 then oldPos else 0
def cfg {s : ℕ} (state : Fin s) (countPos oldPos outputPos : ℕ) (ambient : Fin 27 → List Bool) : Configuration 27 s :=
  ⟨state,heads countPos oldPos outputPos,ambient⟩
def workSlot (j : Fin 19) : Fin 27 :=
  if j.val<8 then ⟨j.val+1,by omega⟩ else if j.val<15 then ⟨j.val+2,by omega⟩ else ⟨j.val+8,by omega⟩
def retainedSlot (i : Fin 27) : Prop := i=0 ∨ i=9 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22
def working (i : Fin 27) : Prop := (i.val<17 ∧ i≠0 ∧ i≠9) ∨ (23 ≤ i.val)
structure Store (b w : ℕ) (bits counts old output : List Bool) (ambient : Fin 27 → List Bool) : Prop where
  factor : ambient 0=frame bits
  width : ambient 9=List.replicate w true
  output : ambient 17=output
  counts : ambient 18=counts
  old : ambient 19=old
  nativeWidth : ambient 20=List.replicate b true
  erase : ambient 21=List.replicate (CompetitorPlane.capacity w) true
  reset : ambient 22=List.replicate (CompetitorPlane.capacity w+1) false
  support : ∀ j,(ambient (workSlot j)).length≤CompetitorPlane.capacity w
noncomputable def clean (w : ℕ) (ambient : Fin 27 → List Bool) := cleared (CompetitorPlane.capacity w) workSlot ambient
def widthSlots : Fin 4 → Fin 27 := ![9,25,24,26]
noncomputable def widthProgram := RecoveryFocus.machine widthSlots ClockUnarySum.machine
noncomputable def widthPrepared (w : ℕ) (ambient : Fin 27 → List Bool) :=
  Function.update (clean w ambient) 24 (ZeroPadding.pad (CompetitorPlane.capacity w) (List.replicate w true))
noncomputable def clearWidthProgram := Composition.machine (clearProgram workSlot) widthProgram
def clearWidthBudget (w : ℕ) := 2*CompetitorPlane.capacity w+2*w+11

theorem work_injective : Function.Injective workSlot := by
  intro i j h
  have hv := congrArg (fun a : Fin 27 => a.val) h
  apply Fin.ext
  simp only [workSlot] at hv
  split_ifs at hv <;> (try simp only at hv) <;> omega
theorem work_avoids (j : Fin 19) (i : Fin 27) (hi : retainedSlot i) : workSlot j≠i := by
  intro h
  have hv := congrArg (fun a : Fin 27 => a.val) h
  simp only [workSlot] at hv
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> split_ifs at hv <;> (try simp only at hv) <;> omega
theorem work_image (i : Fin 27) (hi : working i) : ∃ j,workSlot j=i := by
  rcases hi with ⟨hlt,h0,h9⟩|hlt
  · have hv0 : i.val≠0 := fun h => h0 (Fin.ext h)
    have hv9 : i.val≠9 := fun h => h9 (Fin.ext h)
    by_cases hlo : i.val<9
    · refine ⟨⟨i.val-1,by omega⟩,?_⟩
      apply Fin.ext
      simp [workSlot,show i.val-1<8 by omega]
      omega
    · refine ⟨⟨i.val-2,by omega⟩,?_⟩
      apply Fin.ext
      simp [workSlot,show ¬i.val-2<8 by omega,show i.val-2<15 by omega]
      omega
  · refine ⟨⟨i.val-8,by omega⟩,?_⟩
    apply Fin.ext
    simp [workSlot,show ¬i.val-8<8 by omega,show ¬i.val-8<15 by omega]
    omega
theorem clean_keep (w : ℕ) (ambient : Fin 27 → List Bool) (i : Fin 27) (hi : retainedSlot i) :
    clean w ambient i=ambient i := by
  simp only [clean,cleared,show ¬∃ j,workSlot j=i from fun ⟨j,hj⟩ => work_avoids j i hi hj,if_false]
theorem clean_work (w : ℕ) (ambient : Fin 27 → List Bool) (i : Fin 27) (hi : working i) :
    clean w ambient i=List.replicate (CompetitorPlane.capacity w) false := by
  simp only [clean,cleared,work_image i hi,if_true]

theorem clear_width_run (b w countPos oldPos outputPos : ℕ) (bits counts old output : List Bool)
    (ambient : Fin 27 → List Bool) (h : Store b w bits counts old output ambient) :
    ∃ r,runFrom clearWidthProgram (clearWidthBudget w)
        (cfg clearWidthProgram.start countPos oldPos outputPos ambient)=some r ∧
      r.steps≤clearWidthBudget w ∧ r.final.heads=heads countPos oldPos outputPos ∧
      r.final.tapes=widthPrepared w ambient := by
  have h21 : ∀ j,workSlot j≠21 := fun j => work_avoids j 21 (by simp [retainedSlot])
  have h22 : ∀ j,workSlot j≠22 := fun j => work_avoids j 22 (by simp [retainedSlot])
  have hheads : ∀ j,heads countPos oldPos outputPos (extend workSlot j)=0 := by
    intro j
    rw [extend_cases]
    split
    · have h17 : (workSlot ⟨j.val,‹j.val<19›⟩).val≠17 :=
        fun hv => work_avoids _ 17 (by simp [retainedSlot]) (Fin.ext hv)
      have h18 : (workSlot ⟨j.val,‹j.val<19›⟩).val≠18 :=
        fun hv => work_avoids _ 18 (by simp [retainedSlot]) (Fin.ext hv)
      have h19 : (workSlot ⟨j.val,‹j.val<19›⟩).val≠19 :=
        fun hv => work_avoids _ 19 (by simp [retainedSlot]) (Fin.ext hv)
      simp [heads,h17,h18,h19]
    · split <;> rfl
  obtain ⟨first,hfirst,hfh,hft,hfs⟩ := clear_run workSlot work_injective h21 h22
    (CompetitorPlane.capacity w) (heads countPos oldPos outputPos) ambient h.erase h.reset h.support hheads
  have hcap : w+2≤CompetitorPlane.capacity w := by unfold CompetitorPlane.capacity; nlinarith
  have ready := CompetitorUnaryWidthCopy.copy_ready w (CompetitorPlane.capacity w) hcap
  have htapes : ∀ j,clean w ambient (widthSlots j)=CompetitorUnaryWidthCopy.input w (CompetitorPlane.capacity w) j := by
    intro j
    fin_cases j
    · exact (clean_keep w ambient 9 (by simp [retainedSlot])).trans h.width
    · exact clean_work w ambient 25 (by simp [working])
    · exact clean_work w ambient 24 (by simp [working])
    · exact clean_work w ambient 26 (by simp [working])
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := CompetitorReusableDecision.bounded_focused_run widthSlots (by decide) _ _ _ ready
    (heads countPos oldPos outputPos) (clean w ambient) (by intro j; fin_cases j <;> rfl) htapes
  have houtput : install widthSlots (clean w ambient) (CompetitorUnaryWidthCopy.output w (CompetitorPlane.capacity w))=
      widthPrepared w ambient := by
    funext i
    by_cases h24 : i=24
    · subst i
      rw [widthPrepared,Function.update_self]
      exact install_slot widthSlots (by decide) _ _ 2
    · rw [widthPrepared,Function.update_of_ne h24]
      by_cases h9 : i=9
      · subst i
        exact (install_slot widthSlots (by decide) _ _ 0).trans
          ((clean_keep w ambient 9 (by simp [retainedSlot])).trans h.width).symm
      · by_cases h25 : i=25
        · subst i
          exact (install_slot widthSlots (by decide) _ _ 1).trans (clean_work w ambient 25 (by simp [working])).symm
        · by_cases h26 : i=26
          · subst i
            exact (install_slot widthSlots (by decide) _ _ 3).trans (clean_work w ambient 26 (by simp [working])).symm
          · apply install_other
            intro j hj
            fin_cases j
            · exact h9 hj.symm
            · exact h25 hj.symm
            · exact h24 hj.symm
            · exact h26 hj.symm
  have he : Composition.restart first.final widthProgram.start=
      RecoveryCalls.restarted widthProgram (heads countPos oldPos outputPos) (clean w ambient) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hl' : runFrom widthProgram (2*w+6) (Composition.restart first.final widthProgram.start)=some last := by
    rw [he]
    exact hlast
  have hall := Composition.run_join (clearProgram workSlot) widthProgram _ _ _ first last hfirst hl'
  have htime : (2*CompetitorPlane.capacity w+4)+1+(2*w+6)=clearWidthBudget w := by unfold clearWidthBudget; omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt first last,hall,?_,hlh,hlt.trans houtput⟩
  change first.steps+1+last.steps≤clearWidthBudget w
  unfold clearWidthBudget
  omega

end NearCubicWires.RepairOrdinary.CompetitorPlaneStream
