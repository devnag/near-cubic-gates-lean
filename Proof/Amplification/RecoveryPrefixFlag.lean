import Proof.Amplification.RecoveryPrefixSentinel

/-! One paid local transition copies the oracle answer into the retained
prefix-update flag. Only its first cell changes; false backing is preserved. -/
namespace NearCubicWires.RepairOrdinary.RecoveryPrefixFlag
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 2 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q reads => if q.val=0 then
    some ⟨1,![none,some (reads 0)],fun _ => .stay⟩ else none

theorem copy_ready (cap : Nat) (source : List Bool) (old answer : Bool)
    (ha : readTapeBit source 0=answer) :
    ClockJoin.ReadyRun machine 1
      ![source,ZeroPadding.pad cap [old]] ![source,ZeroPadding.pad cap [answer]] := by
  have hs : step machine (initialConfiguration machine ![source,ZeroPadding.pad cap [old]])=
      some (⟨1,fun _=>0,![source,ZeroPadding.pad cap [answer]]⟩ : Configuration 2 2) := by
    simp only [step,machine,initialConfiguration,Configuration.scanned,Matrix.cons_val_zero,ha]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i
      fin_cases i
      · rfl
      · change writeTapeBit (ZeroPadding.pad cap [old]) 0 answer=ZeroPadding.pad cap [answer]
        exact ZeroPadding.write_pad cap [old] 0 answer
  obtain ⟨r,hr,hf,hstep⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,congrArg Configuration.tapes hf,fun i=>congrFun (congrArg Configuration.heads hf) i,hstep.le⟩

end NearCubicWires.RepairOrdinary.RecoveryPrefixFlag
