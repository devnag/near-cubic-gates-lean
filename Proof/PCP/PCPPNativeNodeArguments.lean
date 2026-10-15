import Proof.PCP.PCPPNativeNodeConst

/-! Executed argument conversion in the whole native-node layout. The
reader's sentinel and the fresh conversion bank supply the focused call;
the resulting raw counter is the actual scalar-emitter input. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem arg_run (right : Bool) (n : ℕ) (heads : Fin 119 → ℕ) (data : Fin 119 → List Bool)
    (hh : ∀ i,heads (argSlots right i)=PCPPNativeTemplateRaw.heads i)
    (ht : ∀ i,data (argSlots right i)=MatrixTemplateCopy.resetInput n i) :
    ∃ r,runFrom (argProgram right) (4*n+16)
      (RecoveryCalls.restarted (argProgram right) heads data)=some r ∧
      r.steps=4*n+16 ∧
      (∀ i,r.final.heads (argSlots right i)=PCPPNativeTemplateRaw.heads i) ∧
      r.final.tapes (argSlots right 0)=UnaryTemplate.tape n ∧
      r.final.tapes (argSlots right 1)=List.replicate n true ∧
      (∀ i,(∀ j,argSlots right j≠i) → r.final.heads i=heads i ∧ r.final.tapes i=data i) := by
  obtain ⟨raw,hr,rs,r0,r1,_,_,rh⟩ := PCPPNativeTemplateRaw.template_run n
  obtain ⟨r,hrun,_,steps,rheads,rtapes,keep⟩ := RecoveryFocus.dock
    (argSlots right) (arg_injective right) PCPPNativeTemplateRaw.machine _ heads data
    (PCPPNativeTemplateRaw.entry n) hh ht raw hr
  refine ⟨r,hrun,steps.trans rs,?_,(rtapes 0).trans r0,(rtapes 1).trans r1,keep⟩
  intro i
  rw [rheads,rh]

theorem arg_work_away (right : Bool) (i : Fin 5) (hi : i≠0) :
    (∀ j,readSlots j≠argSlots right i) ∧ argSlots right i≠0 ∧ argSlots right i≠5 := by
  cases right <;> fin_cases i <;> first | exact False.elim (hi rfl) | decide

theorem arg_work_initial (right : Bool) (i : Fin 5) (hi : i≠0)
    (source queries : List Bool) (pos base position C : ℕ) (out : List Bool) :
    initialHeads pos out (argSlots right i)=0 ∧
      initialData source queries base position C out (argSlots right i)=[] := by
  cases right <;> fin_cases i <;> first | exact False.elim (hi rfl) |
    simp [argSlots,initialHeads,initialData]

theorem initial_field (projected : Bool) (i : Fin 24) (hi : i≠1)
    (source queries : List Bool) (pos base position index C : ℕ) (out : List Bool) :
    initialHeads pos out (fieldSlots projected i)=PCPPNativeAddressReusable.heads out i ∧
      initialData source queries base position C out (fieldSlots projected i)=
        PCPPNativeAddressReusable.data (if projected then 0 else base) index C out i := by
  cases projected <;> fin_cases i <;> first | exact False.elim (hi rfl) |
    simp [fieldSlots,initialHeads,initialData,PCPPNativeAddressReusable.heads,PCPPNativeAddressReusable.data]

theorem field_read_away (projected : Bool) (i : Fin 24) : ∀ j,readSlots j≠fieldSlots projected i := by
  cases projected <;> fin_cases i <;> decide

theorem field_arg_away (i : Fin 24) (hi : i≠1) : ∀ j,argSlots false j≠fieldSlots false i := by
  fin_cases i <;> first | exact False.elim (hi rfl) | decide

end NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
