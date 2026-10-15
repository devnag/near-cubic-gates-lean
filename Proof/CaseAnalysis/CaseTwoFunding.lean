import Proof.CaseAnalysis.CaseTwoLayout
import Proof.CaseAnalysis.CaseTwoLogs

/-! Dock the actual scalar producer at the approved five-input entry.
The original hierarchy word, canonical description and final address stay
untouched while the paid capacity and log drivers are generated. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Cold
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def fundingProgram (K : ℕ):=RecoveryFocus.machine scalarSlots (ColdLogs.machine K)
theorem funding_input (hierarchy description address : List Bool) (R B : ℕ) (j : Fin 57) :
    input hierarchy description address R B (scalarSlots j)=ColdLogs.input R B j:=by
  fin_cases j <;> rfl

theorem funding_run (K R B : ℕ) (hierarchy description address : List Bool) : ∃ A,
    ClockJoin.ReadyRun (fundingProgram K) (ColdLogs.budget K R B) (input hierarchy description address R B) A ∧
      Funded hierarchy description address R B (K*(R+B+1)^4) A:=by
  obtain ⟨out,hr,hR,hB,hC,hF,hL,h6⟩:=ColdLogs.logs_run K R B
  have h:=hr.focus scalarSlots scalar_injective (input hierarchy description address R B)
    (funding_input hierarchy description address R B)
  refine ⟨_,h,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [install_other scalarSlots _ _ 0 (by decide)];rfl
  · rw [install_other scalarSlots _ _ 1 (by decide)];rfl
  · rw [install_other scalarSlots _ _ 2 (by decide)];rfl
  · exact (install_slot scalarSlots scalar_injective _ _ 0).trans hR
  · exact (install_slot scalarSlots scalar_injective _ _ 1).trans hB
  · exact (install_slot scalarSlots scalar_injective _ _ 14).trans hC
  · exact (install_slot scalarSlots scalar_injective _ _ 29).trans hF
  · exact (install_slot scalarSlots scalar_injective _ _ 44).trans hL
  · exact (install_slot scalarSlots scalar_injective _ _ 55).trans h6
  · intro i hi
    have hn : ∀ j,scalarSlots j≠i:=by
      intro j he
      have hj : (scalarSlots j).val<60:=by fin_cases j <;> decide
      have hv:=congrArg Fin.val he
      omega
    rw [install_other scalarSlots _ _ i hn]
    have hn0 : i≠0:=by intro he;subst i;contradiction
    have hn1 : i≠1:=by intro he;subst i;contradiction
    have hn2 : i≠2:=by intro he;subst i;contradiction
    have hn3 : i≠3:=by intro he;subst i;contradiction
    have hn4 : i≠4:=by intro he;subst i;contradiction
    simp only [input,hn0,hn1,hn2,hn3,hn4,if_false]

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Cold
