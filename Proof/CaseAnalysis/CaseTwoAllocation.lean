import Proof.CaseAnalysis.CaseTwoLayout

/-! Allocate every short work tape and both reset-log sizes from their
paid raw drivers. Original inputs and generator outputs remain in place. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Cold
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def smallData (C : ℕ) (A : Fin 135→List Bool) (i : Fin 135):=
  if i=84 then List.replicate (C+1) false
  else if ∃ j,smallWork j=i then List.replicate C false else A i
def longData (C : ℕ) (A : Fin 135→List Bool):=
  Function.update (Function.update (smallData C A) 86 (List.replicate (16*(C+1)) false)) 134
    (List.replicate (16*(C+1)+1) false)
noncomputable def smallProgram:=RecoveryFocus.machine smallSlots (RecoveryScratchErase.resetMachine 25)
noncomputable def longProgram:=RecoveryFocus.machine longSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def allocationProgram:=Composition.machine smallProgram longProgram
def allocationBudget (C : ℕ):=2*C+4+1+(2*(16*(C+1))+4)

theorem small_ge (j : Fin 25) : 60≤(smallWork j).val:=by fin_cases j <;> decide
theorem erase_work (t C : ℕ) (j : Fin t) : eraseOutput t C (j.castAdd 2)=List.replicate C false:=by
  change eraseOutput t C ((j.castAdd 1).castAdd 1)=_
  simp only [eraseOutput,Fin.addCases_left]
theorem small_work (C : ℕ) (A : Fin 135→List Bool) (j : Fin 25) :
    smallData C A (smallWork j)=List.replicate C false:=by
  have hn : smallWork j≠84:=by fin_cases j <;> decide
  simp only [smallData,if_neg hn,if_pos (show ∃ k,smallWork k=smallWork j from ⟨j,rfl⟩)]
theorem small_outside (C : ℕ) (A : Fin 135→List Bool) (i : Fin 135)
    (hi : i≠84) (hw : ∀ j,smallWork j≠i) : smallData C A i=A i:=by
  simp only [smallData,if_neg hi,if_neg (show ¬∃ j,smallWork j=i from by simpa using hw)]
theorem small_old (C : ℕ) (A : Fin 135→List Bool) (i : Fin 135) (hi : i.val<60) : smallData C A i=A i:=by
  apply small_outside
  · intro he;subst i;contradiction
  · intro j he
    have hj:=small_ge j
    have hv:=congrArg Fin.val he
    omega

theorem small_ready (hierarchy description address : List Bool) (R B C : ℕ) (A : Fin 135→List Bool)
    (h : Funded hierarchy description address R B C A) :
    ClockJoin.ReadyRun smallProgram (2*C+4) A (smallData C A):=by
  have run:=(erase_ready 25 C).focus smallSlots small_injective A (by
    intro j
    fin_cases j
    all_goals first | exact h.capacity | exact h.fresh _ (by decide))
  have he : install smallSlots A (eraseOutput 25 C)=smallData C A:=by
    apply HierarchyAllocation.install_eq smallSlots small_injective
    · intro j
      refine Fin.addCases (m:=25) (n:=2) (fun k=>?_) (fun k=>?_) j
      · rw [show smallSlots (k.castAdd 2)=smallWork k from Fin.addCases_left k,erase_work]
        exact small_work C A k
      · fin_cases k
        · change smallData C A 17=List.replicate C true
          rw [small_old C A 17 (by decide)]
          exact h.capacity
        · rfl
    · intro i hi
      apply small_outside
      · intro he;subst i;exact hi 26 rfl
      · intro j hj;exact hi (j.castAdd 2) ((Fin.addCases_left j).trans hj)
  rw [he] at run
  exact run

theorem long_ready (hierarchy description address : List Bool) (R B C : ℕ) (A : Fin 135→List Bool)
    (h : Funded hierarchy description address R B C A) :
    ClockJoin.ReadyRun longProgram (2*(16*(C+1))+4) (smallData C A) (longData C A):=by
  have run:=(erase_ready 1 (16*(C+1))).focus longSlots (by decide) (smallData C A) (by
    intro j;fin_cases j
    · change smallData C A 86=[]
      rw [small_outside C A 86 (by decide) (by decide)]
      exact h.fresh 86 (by decide)
    · change smallData C A 47=List.replicate (16*(C+1)) true
      rw [small_old C A 47 (by decide)]
      exact h.long
    · change smallData C A 134=[]
      rw [small_outside C A 134 (by decide) (by decide)]
      exact h.fresh 134 (by decide))
  have he : install longSlots (smallData C A) (eraseOutput 1 (16*(C+1)))=longData C A:=by
    apply HierarchyAllocation.install_eq longSlots (by decide)
    · intro j;fin_cases j
      · change longData C A 86=List.replicate (16*(C+1)) false
        simp [longData]
      · change longData C A 47=List.replicate (16*(C+1)) true
        simp only [longData,Function.update_of_ne (by decide : (47 : Fin 135)≠134),
          Function.update_of_ne (by decide : (47 : Fin 135)≠86),small_old C A 47 (by decide)]
        exact h.long
      · change longData C A 134=List.replicate (16*(C+1)+1) false
        simp [longData]
    · intro i hi
      have h86 : i≠86:=fun he=>hi 0 he.symm
      have h134 : i≠134:=fun he=>hi 2 he.symm
      simp only [longData,Function.update_of_ne h134,Function.update_of_ne h86]
  rw [he] at run
  exact run

theorem allocation_ready (hierarchy description address : List Bool) (R B C : ℕ) (A : Fin 135→List Bool)
    (h : Funded hierarchy description address R B C A) :
    ClockJoin.ReadyRun allocationProgram (allocationBudget C) A (longData C A):=
  ClockJoin.join _ _ _ _ _ _ _ (small_ready hierarchy description address R B C A h)
    (long_ready hierarchy description address R B C A h)

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Cold
