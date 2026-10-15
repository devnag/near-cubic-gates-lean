import Proof.Hierarchy.CompetitorSameBucketRecordDriver

/-! Actual B-fold record-block length and reusable loop drivers from the
retained H and B fields. Every product, copy and rewind is executed once. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketBlockDrivers
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def native (i : Fin 13) : Fin 24 := if i=0 then 0 else ⟨i.val+1,by omega⟩
def productSlots : Fin 4 → Fin 24 := ![10,1,14,15]
def templateSlots : Fin 5 → Fin 24 := ![14,16,17,18,19]
def copySlots : Fin 5 → Fin 24 := ![1,20,21,22,23]
noncomputable def first := RecoveryFocus.machine native CompetitorSameBucketRecordDriver.machine
noncomputable def product := RecoveryFocus.machine productSlots ClockUnaryProduct.machine
noncomputable def template := RecoveryFocus.machine templateSlots MatrixRawDimension.resetMachine
noncomputable def copy := RecoveryFocus.machine copySlots MatrixTemplateCopy.resetMachine
noncomputable def tail := Composition.machine template copy
noncomputable def middle := Composition.machine product tail
noncomputable def machine := Composition.machine first middle

def input (h b : ℕ) : Fin 24 → List Bool := fun i =>
  if i=0 then List.replicate h true else if i=1 then UnaryTemplate.tape b else []
def budget (h b : ℕ) := CompetitorSameBucketRecordDriver.budget h+1+
  (WilliamsUnaryProduct.budget (4*h+1) b+1+((4*((4*h+1)*b)+8)+1+(4*b+12)))

theorem native_injective : Function.Injective native := by
  intro i j hij
  by_cases hi : i=0
  · subst i
    by_cases hj : j=0
    · exact hj.symm
    · simp [native,hj] at hij
  · by_cases hj : j=0
    · subst j
      simp [native,hi] at hij
    · have hv := congrArg Fin.val hij
      simp only [native,if_neg hi,if_neg hj] at hv
      exact Fin.ext (by omega)

theorem native_avoids (j : Fin 13) (i : Fin 24) (hi : i=1 ∨ 14 ≤ i.val) : native j≠i := by
  intro he
  have hv := congrArg Fin.val he
  unfold native at hv
  split at hv <;> rcases hi with rfl|hi <;> simp_all <;> omega

theorem drivers_ready (h b : ℕ) : ∃ out,ClockJoin.ReadyRun machine (budget h b) (input h b) out ∧
    out 0=List.replicate h true ∧ out 1=UnaryTemplate.tape b ∧
    out 10=List.replicate (4*h+1) true ∧ out 11=List.replicate (4*h+1) true ∧ out 12=UnaryTemplate.tape (4*h+1) ∧
    out 16=List.replicate ((4*h+1)*b) true ∧ out 17=List.replicate ((4*h+1)*b) true ∧
    out 18=UnaryTemplate.tape ((4*h+1)*b) ∧ out 20=List.replicate b true ∧
    out 21=List.replicate b true ∧ out 22=UnaryTemplate.tape b := by
  obtain ⟨record,hrecord,r0,r9,r10,r11⟩ := CompetitorSameBucketRecordDriver.driver_ready h
  let initial := install native (input h b) record
  have hfirst := bounded_focus native native_injective _ _ _ hrecord (input h b)
    (by intro i; fin_cases i <;> rfl)
  have initial_keep (i : Fin 24) (hi : i=1 ∨ 14 ≤ i.val) : initial i=input h b i :=
    install_other native _ _ i (fun j => native_avoids j i hi)
  have hproduct := bounded_focus productSlots (by decide) _ _ _ (CompetitorDimensions.unary_ready (4*h+1) b) initial (by
    intro i
    fin_cases i
    · exact (install_slot native native_injective _ record 9).trans r9
    · exact initial_keep 1 (by simp)
    · exact initial_keep 14 (by simp)
    · exact initial_keep 15 (by simp))
  let multiplied := install productSlots initial (WilliamsUnaryProduct.output (4*h+1) b)
  obtain ⟨base,hbase,b1,b2,b3,bheads,bsteps⟩ := MatrixRawDimension.reset_run ((4*h+1)*b)
  have rawReady : ClockJoin.ReadyRun MatrixRawDimension.resetMachine (4*((4*h+1)*b)+8)
      (MatrixRawDimension.resetInput ((4*h+1)*b)) base.final.tapes := ⟨base,hbase,rfl,bheads,bsteps.le⟩
  have htemplate := bounded_focus templateSlots (by decide) _ _ _ rawReady multiplied (by
    intro i
    fin_cases i
    · exact install_slot productSlots (by decide) _ _ 2
    · exact (install_other productSlots _ _ 16 (by decide)).trans (initial_keep 16 (by simp))
    · exact (install_other productSlots _ _ 17 (by decide)).trans (initial_keep 17 (by simp))
    · exact (install_other productSlots _ _ 18 (by decide)).trans (initial_keep 18 (by simp))
    · exact (install_other productSlots _ _ 19 (by decide)).trans (initial_keep 19 (by simp)))
  let templated := install templateSlots multiplied base.final.tapes
  obtain ⟨copied,hcopied,c0,c1,c2,c3,ch,cs⟩ := MatrixTemplateCopy.reset_run b
  have copyReady : ClockJoin.ReadyRun MatrixTemplateCopy.resetMachine (4*b+12)
      (MatrixTemplateCopy.resetInput b) copied.final.tapes := ⟨copied,hcopied,rfl,ch,cs.le⟩
  have hcopy := bounded_focus copySlots (by decide) _ _ _ copyReady templated (by
    intro i
    fin_cases i
    · exact (install_other templateSlots _ _ 1 (by decide)).trans (install_slot productSlots (by decide) _ _ 1)
    · exact (install_other templateSlots _ _ 20 (by decide)).trans
        ((install_other productSlots _ _ 20 (by decide)).trans (initial_keep 20 (by simp)))
    · exact (install_other templateSlots _ _ 21 (by decide)).trans
        ((install_other productSlots _ _ 21 (by decide)).trans (initial_keep 21 (by simp)))
    · exact (install_other templateSlots _ _ 22 (by decide)).trans
        ((install_other productSlots _ _ 22 (by decide)).trans (initial_keep 22 (by simp)))
    · exact (install_other templateSlots _ _ 23 (by decide)).trans
        ((install_other productSlots _ _ 23 (by decide)).trans (initial_keep 23 (by simp))))
  have htail := ClockJoin.join template copy _ _ _ _ _ htemplate hcopy
  have hmiddle := ClockJoin.join product tail _ _ _ _ _ hproduct htail
  have hall := ClockJoin.join first middle _ _ _ _ _ hfirst hmiddle
  let out := install copySlots templated copied.final.tapes
  have final_keep (i : Fin 24) (hi : i=0 ∨ i=10 ∨ i=11 ∨ i=12) : out i=multiplied i := by
    rcases hi with rfl|rfl|rfl|rfl
    all_goals exact (install_other copySlots _ _ _ (by decide)).trans (install_other templateSlots _ _ _ (by decide))
  refine ⟨out,hall,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (final_keep 0 (by simp)).trans ((install_other productSlots _ _ 0 (by decide)).trans
      ((install_slot native native_injective _ record 0).trans r0))
  · exact (install_slot copySlots (by decide) _ _ 0).trans c0
  · exact (final_keep 10 (by simp)).trans (install_slot productSlots (by decide) _ _ 0)
  · exact (final_keep 11 (by simp)).trans ((install_other productSlots _ _ 11 (by decide)).trans
      ((install_slot native native_injective _ record 10).trans r10))
  · exact (final_keep 12 (by simp)).trans ((install_other productSlots _ _ 12 (by decide)).trans
      ((install_slot native native_injective _ record 11).trans r11))
  · exact (install_other copySlots _ _ 16 (by decide)).trans ((install_slot templateSlots (by decide) _ _ 1).trans b1)
  · exact (install_other copySlots _ _ 17 (by decide)).trans ((install_slot templateSlots (by decide) _ _ 2).trans b2)
  · exact (install_other copySlots _ _ 18 (by decide)).trans ((install_slot templateSlots (by decide) _ _ 3).trans b3)
  · exact (install_slot copySlots (by decide) _ _ 1).trans c1
  · exact (install_slot copySlots (by decide) _ _ 2).trans c2
  · exact (install_slot copySlots (by decide) _ _ 3).trans c3

theorem budget_eq (h b : ℕ) : budget h b=8*(4*h+1)*b+70*h+4*b+83 := by
  unfold budget CompetitorSameBucketRecordDriver.budget WilliamsUnaryProduct.budget
  ring

end NearCubicWires.RepairOrdinary.CompetitorSameBucketBlockDrivers
