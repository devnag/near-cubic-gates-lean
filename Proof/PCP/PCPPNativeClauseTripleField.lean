import Proof.PCP.PCPPNativeClauseTripleLayout

/-! Each of the three original fields uses the same cleared bank and stores
its reference in a distinct retained destination. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseTriple
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem field_run (pre bits tail : List Bool) (index : ℕ) (sign : Bool)
    (stride p n C : ℕ) (refs : Fin 3→List Bool) (target : Fin 3) (empty : refs target=[])
    (hv : value bits=2*index+sign.toNat)
    (hC : PCPPNativeClauseField.budget bits index sign stride p n+1 ≤ C) : ∃ r,
    runFrom (fieldMachine target) (PCPPNativeClauseReusable.budget bits index stride sign p n C)
      (entry (fieldMachine target) pre.length (data (pre++frame bits++tail) stride p n C refs))=some r ∧
      r.final.heads=heads (pre.length+2*bits.length+1) ∧
      r.final.tapes=data (pre++frame bits++tail) stride p n C
        (Function.update refs target (List.replicate (PCPPNativeClauseReusable.reference index stride sign p n) true)) ∧
      r.steps ≤ PCPPNativeClauseReusable.budget bits index stride sign p n C := by
  obtain ⟨base,hb,bh,bt,bs⟩ := PCPPNativeClauseReusable.field_run pre bits tail index sign stride p n C hv hC
  obtain ⟨r,hr,_,rs,rh,rt,keep⟩ := RecoveryFocus.dock (slots target) (injective target)
    PCPPNativeClauseReusable.machine _ (heads pre.length)
    (data (pre++frame bits++tail) stride p n C refs) _
    (fun j=>(field_input (pre++frame bits++tail) stride p n C pre.length refs target j).1)
    (by intro j
        have h := (field_input (pre++frame bits++tail) stride p n C pre.length refs target j).2
        rw [empty] at h
        exact h) base hb
  refine ⟨r,hr,?_,?_,rs.le.trans bs⟩
  · funext i
    by_cases hi : ∃ j,slots target j=i
    · obtain ⟨j,rfl⟩ := hi
      rw [rh,bh]
      exact (field_input (pre++frame bits++tail) stride p n C
        (pre.length+2*bits.length+1) refs target j).1.symm
    · obtain ⟨k,_,he⟩ := (coverage target i).resolve_left hi
      rw [(keep i (by intro j hj; exact hi ⟨j,hj⟩)).1,←he]
      rw [reference_head,reference_head]
  · funext i
    by_cases hi : ∃ j,slots target j=i
    · obtain ⟨j,rfl⟩ := hi
      rw [rt,bt]
      have h := (field_input (pre++frame bits++tail) stride p n C
        (pre.length+2*bits.length+1)
        (Function.update refs target (List.replicate (PCPPNativeClauseReusable.reference index stride sign p n) true)) target j).2
      rw [Function.update_self] at h
      exact h.symm
    · obtain ⟨k,hkt,he⟩ := (coverage target i).resolve_left hi
      rw [(keep i (by intro j hj; exact hi ⟨j,hj⟩)).2,←he,reference_data,reference_data]
      exact (Function.update_of_ne hkt _ _).symm

end NearCubicWires.RepairOrdinary.PCPPNativeClauseTriple
