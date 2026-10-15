import Proof.Amplification.RecoveryPCPFormulaResumeSearchReady

/-! Append the two actual framed search fields with separate blank return
logs. Their emitted concatenation is the literal canonical-search request. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSearchPair
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def leftSlots : Fin 3→Fin 5 := ![0,2,3]
def rightSlots : Fin 3→Fin 5 := ![1,2,4]
theorem left_injective : Function.Injective leftSlots := by decide
theorem right_injective : Function.Injective rightSlots := by decide
noncomputable def first := RecoveryFocus.machine leftSlots CompetitorFrameAppend.machine
noncomputable def last := RecoveryFocus.machine rightSlots CompetitorFrameAppend.machine
noncomputable def machine := Composition.machine first last
def input (left right : List Bool) : Fin 5→List Bool := ![frame left,frame right,[],[],[]]
def budget (left right : List Bool) := (4*left.length+3)+1+(4*right.length+3)

theorem pair_run (left right : List Bool) : ∃ r,
    run machine (budget left right) (input left right)=some r ∧
      r.final.tapes 2=frame left++frame right ∧
      r.final.heads 2=(frame left++frame right).length ∧ r.steps≤budget left right := by
  obtain ⟨l,hl,lf,lSteps⟩ := CompetitorFrameAppend.append_run left [] []
  obtain ⟨a,ha,_ac,aSteps,ah,aT,ak⟩ := RecoveryFocus.dock leftSlots left_injective
    CompetitorFrameAppend.machine _ (fun _ : Fin 5=>0) (input left right)
    (CompetitorFrameAppend.scan 0 (frame left++[]) 0 [])
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> simp [input,leftSlots,CompetitorFrameAppend.scan]) l hl
  have hword : a.final.tapes 2=frame left := by
    have h:=aT 1
    rw [lf] at h
    simpa only [leftSlots,CompetitorFrameAppend.reset,Matrix.cons_val_one,Matrix.cons_val_zero,List.nil_append] using h
  have hhead : a.final.heads 2=(frame left).length := by
    have h:=ah 1
    rw [lf] at h
    simpa only [leftSlots,CompetitorFrameAppend.reset,Matrix.cons_val_one,Matrix.cons_val_zero,List.nil_append] using h
  obtain ⟨r,hr,rf,rSteps⟩ := CompetitorFrameAppend.append_run right [] (frame left)
  have hh : ∀ i : Fin 3,a.final.heads (rightSlots i)=
      (CompetitorFrameAppend.scan 0 (frame right++[]) 0 (frame left)).heads i := by
    intro i; fin_cases i
    · exact (ak 1 (by decide)).1
    · exact hhead
    · exact (ak 4 (by decide)).1
  have ht : ∀ i : Fin 3,a.final.tapes (rightSlots i)=
      (CompetitorFrameAppend.scan 0 (frame right++[]) 0 (frame left)).tapes i := by
    intro i; fin_cases i
    · have h:=(ak 1 (by decide)).2
      change a.final.tapes 1=frame right++[]
      rw [List.append_nil]
      exact h
    · exact hword
    · exact (ak 4 (by decide)).2
  obtain ⟨b,hb,_bc,bSteps,bh,bt,_bk⟩ := RecoveryFocus.dock rightSlots right_injective
    CompetitorFrameAppend.machine _ a.final.heads a.final.tapes _ hh ht r hr
  have whole:=Composition.run_join first last _ _ _ a b ha hb
  refine ⟨_,whole,?_,?_,?_⟩
  · change b.final.tapes (rightSlots 1)=_
    rw [bt,rf]
    rfl
  · change b.final.heads (rightSlots 1)=_
    rw [bh,rf]
    rfl
  · change a.steps+1+b.steps≤_
    rw [aSteps,bSteps,lSteps,rSteps]
    exact Nat.le_refl _

theorem forward : CursorRestore.NoLeft machine 2 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.focus_forward leftSlots left_injective CompetitorFrameAppend.machine 1
      RecoveryPCPFormulaResumeForward.field_append)
    (CursorRestore.focus_forward rightSlots right_injective CompetitorFrameAppend.machine 1
      RecoveryPCPFormulaResumeForward.field_append)

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSearchPair
