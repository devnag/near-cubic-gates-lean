import Proof.Amplification.RecoveryRootLoopExecution
import Proof.Amplification.RecoveryRootDigitSemantics

/-! The complete ordinary digit-loop run. The moving source cursor and all
arithmetic workspace are joined at every actual call boundary. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRootLoop
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRootIteration
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem loop_prefix (ds : List Digit) (original pre : List Bool) (s : Store) (hv : Valid s) :
    Timed machine (time ds s)
      (boundary 0 original (pre ++ frame (RecoveryRootIteration.stream ds)) s pre.length)
      (RecoveryCalls.stopped sizes (heads (pre.length + 4 * ds.length))
        (tapes original (pre ++ frame (RecoveryRootIteration.stream ds)) (iterate ds s))) := by
  induction ds generalizing pre s with
  | nil => simpa [time, iterate, RecoveryRootIteration.stream, frame] using finish_call original pre s
  | cons d ds ih =>
    rcases d with ⟨lowBit, highBit⟩
    have hfirst := digit_call lowBit highBit original pre (RecoveryRootIteration.stream ds) s hv
    have htail := ih (pre ++ [true, highBit, true, lowBit]) (advance (lowBit, highBit) s)
      (advance_valid (lowBit, highBit) s hv)
    have ht : Timed machine (time ds (advance (lowBit, highBit) s))
        (boundary 0 original (pre ++ frame (highBit :: lowBit :: RecoveryRootIteration.stream ds))
          (advance (lowBit, highBit) s) (pre.length + 4))
        (RecoveryCalls.stopped sizes (heads (pre.length + 4 * ((lowBit, highBit) :: ds).length))
          (tapes original (pre ++ frame (highBit :: lowBit :: RecoveryRootIteration.stream ds))
            (iterate ds (advance (lowBit, highBit) s)))) := by
      simpa [frame, List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
    exact hfirst.trans ht

theorem loop_run (ds : List Digit) (original : List Bool) (s : Store) (hv : Valid s) :
    ∃ r : ExecutionReceipt 15 (Fintype.card (RecoveryCalls.Control sizes)),
      run machine (time ds s) (tapes original (frame (RecoveryRootIteration.stream ds)) s) = some r ∧
      r.final.tapes = tapes original (frame (RecoveryRootIteration.stream ds)) (iterate ds s) ∧
      r.final.heads = heads (4 * ds.length) ∧ r.steps = time ds s := by
  have hp := loop_prefix ds original [] s hv
  obtain ⟨r, hr, hf, hs⟩ := hp.run (by simp [machine, RecoveryCalls.machine, RecoveryCalls.stopped])
  have hin : initialConfiguration machine (tapes original (frame (RecoveryRootIteration.stream ds)) s) =
      boundary 0 original ([] ++ frame (RecoveryRootIteration.stream ds)) s 0 := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  refine ⟨r, ?_, ?_, ?_, hs⟩
  · rw [run, hin]; exact hr
  · simp [hf, RecoveryCalls.stopped]
  · simp [hf, RecoveryCalls.stopped]

end NearCubicWires.RepairOrdinary.RecoveryRootLoop
