import Proof.MachineModel.OrdinaryMatrixBucketSizePrepare

/-! The two executed canonical bucket-size branches share one output
template. Their 2U source and all previously produced fields are retained. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketSizeBranches
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def divideSlots : Fin 4 → Fin 28 := ![6,12,16,17]
def copySlots : Fin 5 → Fin 28 := ![16,18,19,20,21]
def smallSlots : Fin 5 → Fin 28 := ![8,18,19,20,21]
noncomputable def divide := RecoveryFocus.machine divideSlots MatrixBucketDivide.machine
noncomputable def copy := RecoveryFocus.machine copySlots MatrixRawDimension.resetMachine
noncomputable def positive := Composition.machine divide copy
noncomputable def small := RecoveryFocus.machine smallSlots MatrixTemplateCopy.resetMachine
def value (U q : ℕ) := if q≤1 then 2*U else (2*U)/(q-1)
def positiveBudget (U q : ℕ) := 8*(2*U)+6+1+(4*((2*U)/(q-1))+8)

theorem positive_run (U q : ℕ) (hq : 1<q) (ambient : Fin 28 → List Bool)
    (h6 : ambient 6=List.replicate (2*U) true) (h12 : ambient 12=UnaryTemplate.tape (q-1))
    (fresh : ∀ i : Fin 28,16 ≤ i.val → ambient i=[]) :
    ∃ out,ClockJoin.ReadyRun positive (positiveBudget U q) ambient out ∧
      (∀ i : Fin 16,out (i.castAdd 12)=ambient (i.castAdd 12)) ∧
      out 18=List.replicate (value U q) true ∧ out 19=List.replicate (value U q) true ∧
      out 20=UnaryTemplate.tape (value U q) ∧ (∀ i : Fin 28,22 ≤ i.val → out i=[]) := by
  obtain ⟨divided,hd,d0,d1,d2,dh,ds⟩ := MatrixBucketDivide.divide_run (2*U) (q-1) (by omega)
  have ready : ClockJoin.ReadyRun MatrixBucketDivide.machine (8*(2*U)+6)
      (MatrixBucketDivide.resetInput (2*U) (q-1)) divided.final.tapes := ⟨divided,hd,rfl,dh,ds⟩
  have hi : ∀ i,ambient (divideSlots i)=MatrixBucketDivide.resetInput (2*U) (q-1) i := by
    intro i; fin_cases i
    · exact h6
    · exact h12
    all_goals exact fresh _ (by decide)
  let stage := install divideSlots ambient divided.final.tapes
  have hp := bounded_focus divideSlots (by decide) _ _ _ ready ambient hi
  have localT (i : Fin 4) : stage (divideSlots i)=divided.final.tapes i := install_slot divideSlots (by decide) _ _ i
  have old (i : Fin 16) : stage (i.castAdd 12)=ambient (i.castAdd 12) := by
    by_cases h6' : i=6
    · subst i; exact (localT 0).trans (d0.trans h6.symm)
    by_cases h12' : i=12
    · subst i; exact (localT 1).trans (d1.trans h12.symm)
    apply install_other
    intro j h
    fin_cases j <;> have hv := congrArg Fin.val h <;> simp [divideSlots] at hv <;> omega
  have untouched (i : Fin 28) (hi : 18 ≤ i.val) : stage i=[] := by
    apply (install_other divideSlots _ _ i ?_).trans (fresh i (by omega))
    intro j h
    fin_cases j <;> have hv := congrArg Fin.val h <;> simp [divideSlots] at hv <;> omega
  obtain ⟨copied,hc,c1,c2,c3,ch,cs⟩ := MatrixRawDimension.reset_run ((2*U)/(q-1))
  have cr : ClockJoin.ReadyRun MatrixRawDimension.resetMachine (4*((2*U)/(q-1))+8)
      (MatrixRawDimension.resetInput ((2*U)/(q-1))) copied.final.tapes := ⟨copied,hc,rfl,ch,cs.le⟩
  have ci : ∀ i,stage (copySlots i)=MatrixRawDimension.resetInput ((2*U)/(q-1)) i := by
    intro i; fin_cases i
    · exact (localT 2).trans d2
    all_goals exact untouched _ (by decide)
  let out := install copySlots stage copied.final.tapes
  have hcopy := bounded_focus copySlots (by decide) _ _ _ cr stage ci
  have whole := ClockJoin.join divide copy _ _ _ _ _ hp hcopy
  have hv : value U q=(2*U)/(q-1) := by simp [value,show ¬q≤1 by omega]
  refine ⟨out,whole,?_,?_,?_,?_,?_⟩
  · intro i
    apply (install_other copySlots _ _ (i.castAdd 12) ?_).trans (old i)
    intro j h
    fin_cases j <;> have hv := congrArg Fin.val h <;> simp [copySlots] at hv <;> omega
  · rw [hv]; exact (install_slot copySlots (by decide) _ _ 1).trans c1
  · rw [hv]; exact (install_slot copySlots (by decide) _ _ 2).trans c2
  · rw [hv]; exact (install_slot copySlots (by decide) _ _ 3).trans c3
  · intro i hi
    apply (install_other copySlots _ _ i ?_).trans (untouched i (by omega))
    intro j h
    fin_cases j <;> have hv := congrArg Fin.val h <;> simp [copySlots] at hv <;> omega

theorem small_run (U q : ℕ) (hq : q≤1) (ambient : Fin 28 → List Bool)
    (h8 : ambient 8=UnaryTemplate.tape (2*U))
    (fresh : ∀ i : Fin 28,16 ≤ i.val → ambient i=[]) :
    ∃ out,ClockJoin.ReadyRun small (4*(2*U)+12) ambient out ∧
      (∀ i : Fin 16,out (i.castAdd 12)=ambient (i.castAdd 12)) ∧
      out 18=List.replicate (value U q) true ∧ out 19=List.replicate (value U q) true ∧
      out 20=UnaryTemplate.tape (value U q) ∧ (∀ i : Fin 28,22 ≤ i.val → out i=[]) := by
  obtain ⟨copied,hc,c0,c1,c2,c3,ch,cs⟩ := MatrixTemplateCopy.reset_run (2*U)
  have cr : ClockJoin.ReadyRun MatrixTemplateCopy.resetMachine (4*(2*U)+12)
      (MatrixTemplateCopy.resetInput (2*U)) copied.final.tapes := ⟨copied,hc,rfl,ch,cs.le⟩
  have ci : ∀ i,ambient (smallSlots i)=MatrixTemplateCopy.resetInput (2*U) i := by
    intro i; fin_cases i
    · exact h8
    all_goals exact fresh _ (by decide)
  let out := install smallSlots ambient copied.final.tapes
  have whole := bounded_focus smallSlots (by decide) _ _ _ cr ambient ci
  have hv : value U q=2*U := by simp [value,hq]
  refine ⟨out,whole,?_,?_,?_,?_,?_⟩
  · intro i
    by_cases hi : i=8
    · subst i; exact (install_slot smallSlots (by decide) _ _ 0).trans (c0.trans h8.symm)
    apply install_other
    intro j h
    fin_cases j <;> have hv := congrArg Fin.val h <;> simp [smallSlots] at hv <;> omega
  · rw [hv]; exact (install_slot smallSlots (by decide) _ _ 1).trans c1
  · rw [hv]; exact (install_slot smallSlots (by decide) _ _ 2).trans c2
  · rw [hv]; exact (install_slot smallSlots (by decide) _ _ 3).trans c3
  · intro i hi
    apply (install_other smallSlots _ _ i ?_).trans (fresh i (by omega))
    intro j h
    fin_cases j <;> have hv := congrArg Fin.val h <;> simp [smallSlots] at hv <;> omega

end NearCubicWires.RepairOrdinary.MatrixBucketSizeBranches
