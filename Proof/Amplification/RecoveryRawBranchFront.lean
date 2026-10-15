import Proof.Amplification.RecoveryRawBranchChecked

/-! The successful frontend's actual flags choose the default, bound-
rejection or SAT continuation. The produced count stays in its shared slot. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawBranch
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem checked_front (x : State) (word : List Bool) (k : Nat)
    (first : ExecutionReceipt 136 (sizes 0))
    (hr : runFrom viewMachine (RecoveryRawViewEntry.budget x.view) (cfg x 0 viewMachine.start)=some first)
    (hf : first.final=cfg (output x word k) (total x word k) first.final.control)
    (hv : first.final.scanned 28=true) :
    ∃ n,n ≤ RecoveryRawViewEntry.budget x.view+1 ∧
      Timed machine n (cfg x 0 machine.start) (checkedCfg (output x word k) (total x word k)) := by
  cases ht : (output x word k).view.inner.tags
  · have hn : next 0 first.final.control first.final.scanned=some 2 := by
      simp only [next,hv,ite_true]
      rw [hf]
      simp only [tags_bit,ht,Bool.false_eq_true,ite_false]
      rfl
    obtain ⟨n,hn,h⟩ := call_receipt sizes programs 0 next 0 2 (RecoveryRawViewEntry.budget x.view)
      (cfg x 0 viewMachine.start) first hr hn
    have he : controlConfig (RecoveryCalls.code sizes 2)
        (RecoveryCalls.restarted (programs 2) first.final.heads first.final.tapes)=
        checkedCfg (output x word k) (total x word k) := by
      rw [hf]
      simp only [checkedCfg,ht,Bool.false_eq_true,ite_false]
      rfl
    rw [he] at h
    exact ⟨n,hn,h⟩
  · cases hb : (output x word k).view.inner.bounded
    · have hn : next 0 first.final.control first.final.scanned=some 3 := by
        simp only [next,hv,ite_true]
        rw [hf]
        simp only [tags_bit,ht,bounded_bit,hb,ite_true,Bool.false_eq_true,ite_false]
        rfl
      obtain ⟨n,hn,h⟩ := call_receipt sizes programs 0 next 0 3 (RecoveryRawViewEntry.budget x.view)
        (cfg x 0 viewMachine.start) first hr hn
      have he : controlConfig (RecoveryCalls.code sizes 3)
          (RecoveryCalls.restarted (programs 3) first.final.heads first.final.tapes)=
          checkedCfg (output x word k) (total x word k) := by
        rw [hf]
        simp only [checkedCfg,ht,hb,ite_true,Bool.false_eq_true,ite_false]
        rfl
      rw [he] at h
      exact ⟨n,hn,h⟩
    · have hn : next 0 first.final.control first.final.scanned=some 1 := by
        simp only [next,hv,ite_true]
        rw [hf]
        simp only [tags_bit,ht,bounded_bit,hb,ite_true]
        rfl
      obtain ⟨n,hn,h⟩ := call_receipt sizes programs 0 next 0 1 (RecoveryRawViewEntry.budget x.view)
        (cfg x 0 viewMachine.start) first hr hn
      have he : controlConfig (RecoveryCalls.code sizes 1)
          (RecoveryCalls.restarted (programs 1) first.final.heads first.final.tapes)=
          checkedCfg (output x word k) (total x word k) := by
        rw [hf]
        simp only [checkedCfg,ht,hb,ite_true]
        rfl
      rw [he] at h
      exact ⟨n,hn,h⟩

end NearCubicWires.RepairOrdinary.RecoveryRawBranch
