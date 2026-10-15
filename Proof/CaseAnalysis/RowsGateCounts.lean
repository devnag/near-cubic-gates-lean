import Proof.CaseAnalysis.RowsGatePairHeads
import Proof.CaseAnalysis.RowsGateTemplateCheck

/-! Both actual gate list counts are compared with the retained source
domain. The first comparison guards the second; its final flag therefore
conjoins the checks without another Boolean machine or tape. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateCounts
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CloseoutRowsGatePairHeads
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads : Fin 5 → ℕ := ![0,0,1,0,0]
def data (n k m : ℕ) (a b : List Bool) : Fin 5 → List Bool :=
  ![CompareMachine.word n,CompareMachine.word k,UnaryTemplate.tape m,a,b]
def leftSlots : Fin 3 → Fin 5 := ![0,2,3]
def rightSlots : Fin 3 → Fin 5 := ![1,2,4]
theorem left_injective : Function.Injective leftSlots := by decide
theorem right_injective : Function.Injective rightSlots := by decide
noncomputable def first := RecoveryFocus.machine leftSlots CloseoutRowsGateTemplateCheck.machine
noncomputable def second := RecoveryFocus.machine rightSlots CloseoutRowsGateTemplateCheck.machine
noncomputable def machine := CloseoutRowsGateColdPair.machine first second (fun bits => bits 3)
def output (n k m : ℕ) := data n k m [decide (n=m)] (if n=m then [decide (k=m)] else [])
def budget (n k m : ℕ) := (2*min n m+3)+1+(2*min k m+3)+1

theorem first_run (n k m : ℕ) :
    ReadyAt first (2*min n m+3) heads (data n k m [] []) (data n k m [decide (n=m)] []) := by
  obtain ⟨base,hbase,bf,bs⟩ := CloseoutRowsGateTemplateCheck.template_run n m
  obtain ⟨r,hr,hf,hs⟩ := RecoveryFocus.run_config leftSlots left_injective
    CloseoutRowsGateTemplateCheck.machine heads (data n k m [] []) _ _ base hbase
  have initial : RecoveryFocus.config leftSlots heads (data n k m [] [])
      (CloseoutRowsGateTemplateCheck.entry n m)=RecoveryCalls.restarted first heads (data n k m [] []) := by
    exact WilliamsSourceCrop.focus_same leftSlots (⟨0,heads,data n k m [] []⟩ : Configuration 5 4)
      (CloseoutRowsGateTemplateCheck.entry n m)
      (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
  rw [initial] at hr
  have final : r.final=⟨3,heads,data n k m [decide (n=m)] []⟩ := by
    rw [hf,bf]
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick leftSlots i with
      | none => simp only [RecoveryFocus.config,hp]
      | some j =>
        have he := RecoveryFocus.slot_of_pick leftSlots hp
        rw [← he]
        simp only [RecoveryFocus.config,RecoveryFocus.pick_slot leftSlots left_injective]
        fin_cases j <;> rfl
    · change install leftSlots (data n k m [] []) (CloseoutRowsGateTemplateCheck.data n m [decide (n=m)])=_
      apply HierarchyAllocation.install_eq _ left_injective
      · intro i;fin_cases i <;> rfl
      · intro i hi
        have h3 : i≠3 := by intro h;exact hi 2 h.symm
        fin_cases i <;> simp_all [data]
  exact ⟨r,hr,by rw [final],by rw [final],(hs.trans bs).le⟩

theorem second_run (n k m : ℕ) (flag : List Bool) :
    ReadyAt second (2*min k m+3) heads (data n k m flag []) (data n k m flag [decide (k=m)]) := by
  obtain ⟨base,hbase,bf,bs⟩ := CloseoutRowsGateTemplateCheck.template_run k m
  obtain ⟨r,hr,hf,hs⟩ := RecoveryFocus.run_config rightSlots right_injective
    CloseoutRowsGateTemplateCheck.machine heads (data n k m flag []) _ _ base hbase
  have initial : RecoveryFocus.config rightSlots heads (data n k m flag [])
      (CloseoutRowsGateTemplateCheck.entry k m)=RecoveryCalls.restarted second heads (data n k m flag []) := by
    exact WilliamsSourceCrop.focus_same rightSlots (⟨0,heads,data n k m flag []⟩ : Configuration 5 4)
      (CloseoutRowsGateTemplateCheck.entry k m)
      (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
  rw [initial] at hr
  have final : r.final=⟨3,heads,data n k m flag [decide (k=m)]⟩ := by
    rw [hf,bf]
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick rightSlots i with
      | none => simp only [RecoveryFocus.config,hp]
      | some j =>
        have he := RecoveryFocus.slot_of_pick rightSlots hp
        rw [← he]
        simp only [RecoveryFocus.config,RecoveryFocus.pick_slot rightSlots right_injective]
        fin_cases j <;> rfl
    · change install rightSlots (data n k m flag []) (CloseoutRowsGateTemplateCheck.data k m [decide (k=m)])=_
      apply HierarchyAllocation.install_eq _ right_injective
      · intro i;fin_cases i <;> rfl
      · intro i hi
        have h4 : i≠4 := by intro h;exact hi 2 h.symm
        fin_cases i <;> simp_all [data]
  exact ⟨r,hr,by rw [final],by rw [final],(hs.trans bs).le⟩

theorem counts_run (n k m : ℕ) :
    ReadyAt machine (budget n k m) heads (data n k m [] []) (output n k m) := by
  by_cases he : n=m
  · have h := joined first second (fun bits => bits 3) _ _ heads _ _ _
      (first_run n k m) (second_run n k m [decide (n=m)]) (by simp [data,heads,he,readTapeBit])
    simpa only [machine,budget,output,if_pos he] using h
  · have h := rejected first second (fun bits => bits 3) _ heads _ _
      (first_run n k m) (by simp [data,heads,he,readTapeBit])
    have more := enlarge _ _ (budget n k m) heads _ _ h (by unfold budget;omega)
    simpa only [machine,output,if_neg he] using more

theorem decision_exact (n k m : ℕ) :
    readTapeBit (output n k m 4) 0=true ↔ n=m ∧ k=m := by
  by_cases he : n=m <;> simp [output,data,he,readTapeBit]

theorem budget_bound (n k m B : ℕ) (hn : n≤B+1) (hk : k≤B+1) :
    budget n k m ≤ 4*B+12 := by
  have h1 := Nat.min_le_left n m
  have h2 := Nat.min_le_left k m
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsGateCounts
