import Proof.PCP.PCPPNativeNodeProjectedConst

/-! Convert the actual Compare.word from projection unpairing to the
retained raw index consumed by the two-node input emitter. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
open LocalBitMultitape RepairRepresentation RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem value_input (n : ℕ) (heads : Fin 119 → ℕ) (data : Fin 119 → List Bool)
    (hh : heads 15=1) (ht : data 15=CompareMachine.word n)
    (work : ∀ i : Fin 5,i≠0 → heads (valueSlots i)=0 ∧ data (valueSlots i)=[]) :
    (∀ i,heads (valueSlots i)=PCPPNativeTemplateRaw.heads i) ∧
      (∀ i,data (valueSlots i)=MatrixTemplateCopy.wordInput n i) := by
  constructor
  · intro i
    by_cases hi : i=0
    · subst i; exact hh
    · simpa only [PCPPNativeTemplateRaw.heads,hi,ite_false] using (work i hi).1
  · intro i
    fin_cases i
    · exact ht
    all_goals exact (work _ (by decide)).2

theorem value_run (n : ℕ) (heads : Fin 119 → ℕ) (data : Fin 119 → List Bool)
    (hh : ∀ i,heads (valueSlots i)=PCPPNativeTemplateRaw.heads i)
    (ht : ∀ i,data (valueSlots i)=MatrixTemplateCopy.wordInput n i) :
    ∃ r,runFrom valueProgram (4*n+16)
      (RecoveryCalls.restarted valueProgram heads data)=some r ∧ r.steps=4*n+16 ∧
      (∀ i,r.final.heads (valueSlots i)=PCPPNativeTemplateRaw.heads i) ∧
      r.final.tapes 11=List.replicate n true ∧
      (∀ i,(∀ j,valueSlots j≠i) → r.final.heads i=heads i ∧ r.final.tapes i=data i) := by
  obtain ⟨raw,hr,rs,r1,_,_,rh⟩ := PCPPNativeTemplateRaw.word_run n
  obtain ⟨r,hrun,_,steps,rheads,rtapes,keep⟩ := RecoveryFocus.dock
    valueSlots value_injective PCPPNativeTemplateRaw.machine _ heads data
    (PCPPNativeTemplateRaw.wordEntry n) hh ht raw hr
  refine ⟨r,hrun,steps.trans rs,?_,(rtapes 1).trans r1,keep⟩
  intro i
  rw [rheads,rh]

theorem value_work_away (i : Fin 5) (hi : i≠0) :
    (∀ j,readSlots j≠valueSlots i) ∧ (∀ j,lookupSlots j≠valueSlots i) ∧ valueSlots i≠14 := by
  fin_cases i <;> first | exact False.elim (hi rfl) | decide

theorem value_work_initial (i : Fin 5) (hi : i≠0)
    (source queries : List Bool) (pos base position C : ℕ) (out : List Bool) :
    initialHeads pos out (valueSlots i)=0 ∧ initialData source queries base position C out (valueSlots i)=[] := by
  fin_cases i <;> first | exact False.elim (hi rfl) | simp [valueSlots,initialHeads,initialData]

theorem field_lookup_away (projected : Bool) (i : Fin 24) : ∀ j,lookupSlots j≠fieldSlots projected i := by
  cases projected <;> fin_cases i <;> decide

theorem field_value_away (i : Fin 24) (hi : i≠1) : ∀ j,valueSlots j≠fieldSlots true i := by
  fin_cases i <;> first | exact False.elim (hi rfl) | decide

theorem field_kind_away (i : Fin 24) : fieldSlots true i≠14 := by fin_cases i <;> decide

end NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
