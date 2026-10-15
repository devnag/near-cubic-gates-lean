import Proof.CaseAnalysis.ScheduleStepLoad

/-! The executed test returns every retained port and its entire scratch
bound to the conditional update. No successful-shape assumption is used. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Step
open LocalBitMultitape RepairOrdinary RecoveryRootRound ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def sourceTarget (sources : EightSources) (k D : Nat) :=
  testSlots sources k D (Test.old sources k D (Candidate.powerSlots sources k D 13))
def flagTarget (sources : EightSources) (k D : Nat) := testSlots sources k D (Test.extra sources k D 3)
theorem test_away (sources : EightSources) (k D : Nat) (i : Fin (tapes sources k D))
    (hi : Test.tapes sources k D ≤ i.val) : ∀ j,testSlots sources k D j≠i := by
  intro j he;have hv:=congrArg Fin.val he;have:=j.isLt
  change j.val=i.val at hv;omega
theorem loaded_outside (sources : EightSources) (k D C s n best : Nat) (i : Fin (tapes sources k D))
    (hi : Test.tapes sources k D ≤ i.val) : loaded sources k D C s n best i=bank sources k D C s n best i := by
  have hnl : i≠lengthTarget sources k D := by
    intro he;have hv:=congrArg Fin.val he
    change i.val=Candidate.tapes sources k D at hv
    dsimp [Test.tapes] at hi;omega
  have hni : i≠indexTarget sources k D := by
    apply ne_index
    dsimp [Test.tapes] at hi;omega
  rw [loaded,Function.update_of_ne hnl,indexed,Function.update_of_ne hni]

theorem test_run (sources : EightSources) (k D copies : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (s n C best : Nat) (hD : 1 ≤ D)
    (hs : s ≤ C) (hn : n ≤ C) (hC : Test.budget sources k D copies clock s n+1 ≤ C) : ∃ out,
    ClockJoin.ReadyRun (test sources k D copies clock) (Test.budget sources k D copies clock s n)
      (loaded sources k D C s n best) out ∧
    (∀ i,out (port sources k D i)=persistent C s n best i) ∧
    (∀ i,(out (work sources k D i)).length ≤ C) ∧
    out (copyLog sources k D 2)=List.replicate C false ∧
    out (sourceTarget sources k D)=ZeroPadding.pad C (UnaryTemplate.tape (2^s)) ∧
    out (flagTarget sources k D)=ZeroPadding.pad C
      [decide (CloseoutLanguage.widthAt sources k clock copies D s ≤ n/2)] := by
  obtain ⟨a,ha,hN,_,hflag,hsize⟩:=Reusable.test sources k D copies clock s n C hD hs hn hC
  have hf:=ha.focus (testSlots sources k D) (test_injective sources k D)
    (loaded sources k D C s n best) (loaded_input sources k D C s n best)
  let out:=install (testSlots sources k D) (loaded sources k D C s n best) a
  have ho (i : Fin (tapes sources k D)) (hi : Test.tapes sources k D ≤ i.val) :
      out i=bank sources k D C s n best i := by
    rw [show out i=loaded sources k D C s n best i from install_other _ _ _ _ (test_away sources k D i hi)]
    exact loaded_outside sources k D C s n best i hi
  refine ⟨out,hf,?_,?_,?_,?_,?_⟩
  · intro i
    rw [ho _ (by change Test.tapes sources k D ≤ workTapes sources k D+i.val;dsimp [workTapes];omega)]
    exact bank_port sources k D C s n best i
  · intro i
    refine Fin.addCases (m:=Test.tapes sources k D) (n:=3) (fun j=>?_) (fun j=>?_) i
    · change (out (testSlots sources k D j)).length ≤ C
      rw [show out (testSlots sources k D j)=a j from install_slot _ (test_injective sources k D) _ _ j]
      exact hsize j
    · rw [ho _ (by change Test.tapes sources k D ≤ Test.tapes sources k D+j.val;omega)]
      rw [bank_work,List.length_replicate]
  · rw [ho _ (by change Test.tapes sources k D ≤ Test.tapes sources k D+2;omega)]
    exact bank_work sources k D C s n best _
  · exact (install_slot _ (test_injective sources k D) _ _ _).trans hN
  · exact (install_slot _ (test_injective sources k D) _ _ _).trans hflag

end
end NearCubicWires.RepairSource.CloseoutSchedule.Step
