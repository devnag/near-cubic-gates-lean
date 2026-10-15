import Proof.Amplification.RecoveryReadyCalls

/-! The restoring loop's constant seed is written from blank tapes. Its
three-bit zero words, comparison flag and reset marks are actual output. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRootInitialization
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def zeroWord : List Bool := [false, false, false]

def rawMachine : Machine 3 8 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 7
  rule := fun q _ =>
    if h : q.val < 7 then some ⟨⟨q.val + 1, by omega⟩,
      ![some ((frame zeroWord).getD q.val false), some ((frame zeroWord).getD q.val false),
        if q.val = 0 then some false else none], ![.right, .right, .stay]⟩
    else none

def sourceReceipt : ExecutionReceipt 3 8 :=
  (run rawMachine 7 (fun _ => [])).get (by decide)

theorem source_run : run rawMachine 7 (fun _ => []) = some sourceReceipt :=
  Option.eq_some_of_isSome _

theorem source_tapes : sourceReceipt.final.tapes = ![frame zeroWord, frame zeroWord, [false]] := by
  funext i
  fin_cases i <;> decide

theorem source_steps : sourceReceipt.steps = 7 := by decide

def machine : Machine 4 10 := Rewind.machine rawMachine

theorem initialize_ready : ReadyRun machine 16 (fun _ => [])
    ![frame zeroWord, frame zeroWord, [false], List.replicate 7 false] := by
  obtain ⟨r, hr, ht, hc, hh, hs, _⟩ := Rewind.Workspace.reset_workspace rawMachine 7
    (fun _ => []) sourceReceipt source_run 0
  have he : 2 * sourceReceipt.steps + 2 = 16 := by rw [source_steps]
  rw [he] at hr
  refine ⟨r, ?_, ?_, hh, hs.trans he⟩
  · change run (Rewind.machine rawMachine) 16 (fun _ => []) = some r
    convert hr using 2
    funext i; fin_cases i <;> rfl
  · funext i; fin_cases i
    · simpa [source_tapes] using ht 0
    · simpa [source_tapes] using ht 1
    · simpa [source_tapes] using ht 2
    · simpa [source_steps] using hc

end NearCubicWires.RepairOrdinary.RecoveryRootInitialization
