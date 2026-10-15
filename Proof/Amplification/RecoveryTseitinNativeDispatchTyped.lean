import Proof.Amplification.RecoveryTseitinNativeDispatch

/-! The executed native tag controller selects precisely the original
Boolean node's clause plan, retaining the source and all kernel cursors. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.NodeController
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem dispatch_run {n z : Nat} (node : BooleanNode n) (ambient : Configuration 1335 z)
    (hh : ambient.heads 1072=1)
    (hd : ambient.tapes 1072=UnaryTemplate.tape (PCPPRequestNodeSchema.tag node).val)
    (hv : ambient.heads 1082=1)
    (dv : ambient.tapes 1082=UnaryTemplate.tape (PCPPRequestNodeSchema.fields node 1)) :
    ∃ time head,time≤6 ∧ Timed machine time (boundary 0 ambient.heads ambient.tapes)
      (boundary (nodeStage (RecoveryTseitinNode.kind node)) head ambient.tapes) ∧
      (∀ flag i,head (kernelSlots flag i)=ambient.heads (kernelSlots flag i)) ∧
      (∀ i,i≠1072 → i≠1082 → head i=ambient.heads i) := by
  cases node with
  | const b=>
    obtain ⟨head,h,hk,ho⟩:=constant_dispatch b ambient hh hd hv dv
    exact ⟨b.toNat+4,head,by cases b <;> decide,h,hk,ho⟩
  | input j=>
    obtain ⟨head,h,hk,ho⟩:=nonconstant_dispatch 1 (by decide) ambient hh hd
    exact ⟨3,head,by decide,h,hk,ho⟩
  | not j=>
    obtain ⟨head,h,hk,ho⟩:=nonconstant_dispatch 2 (by decide) ambient hh hd
    exact ⟨4,head,by decide,h,hk,ho⟩
  | and j k=>
    obtain ⟨head,h,hk,ho⟩:=nonconstant_dispatch 3 (by decide) ambient hh hd
    exact ⟨5,head,by decide,h,hk,ho⟩
  | or j k=>
    obtain ⟨head,h,hk,ho⟩:=nonconstant_dispatch 4 (by decide) ambient hh hd
    exact ⟨6,head,by decide,h,hk,ho⟩

theorem node_stop (k : Fin 6) (fuel : Nat) (head : Fin 1335→Nat) (data : Fin 1335→List Bool)
    (r : ExecutionReceipt 1335 (RecoveryTseitinNode.states (RecoveryTseitinNode.plans k)))
    (hr : runFrom (nodeProgram k) fuel (RecoveryCalls.restarted (nodeProgram k) head data)=some r) :
    Timed machine (r.steps+1) (boundary (nodeStage k) head data)
      (RecoveryCalls.stopped sizes r.final.heads r.final.tapes) := by
  fin_cases k
  · exact stop_run 2 fuel head data r hr (by simp [next])
  · exact stop_run 3 fuel head data r hr (by simp [next])
  · exact stop_run 4 fuel head data r hr (by simp [next])
  · exact stop_run 5 fuel head data r hr (by simp [next])
  · exact stop_run 6 fuel head data r hr (by simp [next])
  · exact stop_run 7 fuel head data r hr (by simp [next])

end NearCubicWires.RepairSource.RecoveryTseitinNative.NodeController
