import Proof.CaseAnalysis.CommonPrepareLayout

/-! The complete physical preparation before original recovery: compute the
shared capacity from the final address and the hierarchy word from the actual
refuter answer. Both original source programs and the connecting step are paid. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCommonPrepare
open LocalBitMultitape RepairSource RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem run {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (A B0 : ℕ)
    (address answer : List Bool) : ∃ out,
    ClockJoin.ReadyRun (machine k H.coefficient A B0)
      (budget k H.coefficient A B0 address answer) (input k address answer) out ∧
    out (addressSlot k)=frame address ∧
    out (capacitySlot k)=List.replicate (CloseoutCapacity.capacity A B0 address.length) true ∧
    out (hierarchySlot k)=frame answer++frame (H.time answer.length).bits:=by
  obtain ⟨capacity,hcap,hW,_hTemplate,haddress⟩:=CloseoutCapacity.capacity_run A B0 address
  have hfirst:=hcap.focus (capacitySlots k) (capacity_injective k)
    (input k address answer) (capacity_input k address answer)
  let middle:=install (capacitySlots k) (input k address answer) capacity
  obtain ⟨request,hreq,hword⟩:=CloseoutHierarchyRequest.request_run H answer
  have hlast:=hreq.focus (requestSlots k)
    (CloseoutHierarchyRequest.Shared.bank_injective k (1 : Fin 27)) middle (by
      intro j
      exact (install_other (capacitySlots k) (input k address answer) capacity
        (requestSlots k j) (fun i=>disjoint k i j)).trans (request_input k address answer j))
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ hfirst hlast,?_,?_,?_⟩
  · exact (install_other (requestSlots k) middle request (capacitySlots k 0)
      (fun j=>Ne.symm (disjoint k 0 j))).trans
        ((install_slot (capacitySlots k) (capacity_injective k) (input k address answer)
          capacity 0).trans haddress)
  · exact (install_other (requestSlots k) middle request (capacitySlots k 24)
      (fun j=>Ne.symm (disjoint k 24 j))).trans
        ((install_slot (capacitySlots k) (capacity_injective k) (input k address answer)
          capacity 24).trans hW)
  · exact (install_slot (requestSlots k)
      (CloseoutHierarchyRequest.Shared.bank_injective k (1 : Fin 27)) middle request
      (CloseoutHierarchyRequest.fresh k 0)).trans hword

end
end NearCubicWires.RepairOrdinary.CloseoutCommonPrepare
