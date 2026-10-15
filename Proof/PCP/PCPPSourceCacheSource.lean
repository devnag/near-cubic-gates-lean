import Proof.PCP.PCPPSourceCacheLayout

/-! The original source call leaves exactly the cold shared-bank input ready.
Only its output head is needed; unrelated source scratch heads stay untouched. -/
namespace NearCubicWires.RepairOrdinary.PCPPSourceCache
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem source_run (a : PointwisePCPPAlgorithm) (request : PCPPRequest a.minimumArity) :
    ∃ r,run (sourceMachine a) (PCPPRequestSource.budget a request) (input a request)=some r ∧
      (∀ j : Fin (coldTapes a),r.final.tapes (coldSlots a j)=
        PCPPQueryCold.input (degree a) (pcppOutput request (a.output request)) request.circuit.size request.arity j) ∧
      (∀ j : Fin (coldTapes a),r.final.heads (coldSlots a j)=0) ∧
      r.steps≤PCPPRequestRuntime.sourceCoefficient a*
        (PCPPRequestRuntime.sourceParameter request.circuit)^(PCPPRequestRuntime.sourceDegree a) := by
  obtain ⟨raw,hr,rt,rh,rs⟩:=PCPPRequestRuntime.cold_source_bound a request
  obtain ⟨out,ho,_,os,oh,ot,keep⟩:=RecoveryFocus.dock (sourceSlots a) (source_injective a)
    (PCPPRequestSource.machine a) _ (fun _=>0) (input a request)
    (initialConfiguration (PCPPRequestSource.machine a) (fun j=>if j.val=0 then nativeWord a request else []))
    (by intro j; rfl) (source_input a request) raw hr
  refine ⟨out,ho,?_,?_,os.le.trans rs⟩
  · intro j
    by_cases hj : j.val=0
    · have he : j=⟨0,by have h:=cold_lower a; omega⟩ := Fin.ext hj
      rw [he,←source_output_slot a]
      exact (ot (PCPPRequestSource.outputSlot a)).trans rt
    · rw [(keep (coldSlots a j) (source_other a j hj)).2]
      exact cold_input_other a request _ j hj
  · intro j
    by_cases hj : j.val=0
    · have he : j=⟨0,by have h:=cold_lower a; omega⟩ := Fin.ext hj
      rw [he,←source_output_slot a]
      exact (oh (PCPPRequestSource.outputSlot a)).trans rh
    · exact (keep (coldSlots a j) (source_other a j hj)).1

end NearCubicWires.RepairOrdinary.PCPPSourceCache
