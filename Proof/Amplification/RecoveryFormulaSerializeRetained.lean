import Proof.Amplification.RecoveryFormulaSerialize

/-! The same accepted serializer also retains its already produced framed
payload and its actual zero head. The next oracle caller copies that frame
with the existing field copier; it need not reconstruct or trim a code. -/
namespace NearCubicWires.RepairSource.RecoveryFormulaSerialize
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open ProjectionNormalization PCPSerializerMass
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem tail_retained (fields : List (List Bool)) : ∃ r,
    run tailMachine (1+1+PCPTraversal.budget (mass fields)) (prepared fields)=some r ∧
      r.final.tapes 78=ZeroPadding.pad (PCPPairReusable.capacity (mass fields)) (frame (PCPTraversal.code fields).bits) ∧
      r.final.heads 78=0 ∧ r.steps ≤ 1+1+PCPTraversal.budget (mass fields) := by
  obtain ⟨first,hfirst,hf,hs⟩ := shift_run (prepared fields)
  obtain ⟨last,hlast,h77,_h78,_h0,_h2,hh,_hother,hsteps⟩ := PCPTraversal.focused_run nativeSlots native_injective
    [] fields [] driverHeads (prepared fields) native_heads (by
      intro j
      simpa only [List.nil_append,List.append_nil] using prepared_native fields j)
  have hrestart : Composition.restart first.final serializeMachine.start=
      (⟨PCPTraversal.machine.start,driverHeads,prepared fields⟩ : Configuration 131 _) := by rw [hf]; rfl
  have hlast' : runFrom serializeMachine (PCPTraversal.budget (mass fields))
      (Composition.restart first.final serializeMachine.start)=some last := by rw [hrestart]; exact hlast
  have hwhole := Composition.run_join shift serializeMachine 1 (PCPTraversal.budget (mass fields))
    _ first last hfirst hlast'
  refine ⟨_,hwhole,h77,?_,?_⟩
  · exact hh 77
  · change first.steps+1+last.steps ≤ _
    omega

private theorem restart_of_ready {t a b : Nat} (q : Machine t b)
    (c : Configuration t a) (output : Fin t→List Bool)
    (ht : c.tapes=output) (hh : ∀ i,c.heads i=0) :
    Composition.restart c q.start=initialConfiguration q output := by
  apply configuration_ext
  · rfl
  · exact funext hh
  · exact ht

theorem retained_run (fields : List (List Bool)) : ∃ r,
    run machine (rawBudget fields) (input fields)=some r ∧
      r.final.tapes 78=ZeroPadding.pad (PCPPairReusable.capacity (mass fields)) (frame (PCPTraversal.code fields).bits) ∧
      r.final.heads 78=0 ∧ r.steps ≤ rawBudget fields := by
  obtain ⟨first,hfirst,hft,hfh,hfs⟩ := prepare_ready fields
  obtain ⟨last,hlast,hout,hh,hls⟩ := tail_retained fields
  have he := restart_of_ready tailMachine first.final (prepared fields) hft hfh
  have hlast' : runFrom tailMachine (1+1+PCPTraversal.budget (mass fields))
      (Composition.restart first.final tailMachine.start)=some last := by rw [he]; exact hlast
  have hwhole := Composition.run_join prepareMachine tailMachine (prepareBudget fields)
    (1+1+PCPTraversal.budget (mass fields)) _ first last hfirst hlast'
  refine ⟨_,hwhole,hout,hh,?_⟩
  change first.steps+1+last.steps ≤ rawBudget fields
  unfold rawBudget
  omega

end NearCubicWires.RepairSource.RecoveryFormulaSerialize
