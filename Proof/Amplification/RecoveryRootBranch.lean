import Proof.Amplification.RecoveryRootController

namespace NearCubicWires.RepairOrdinary.RecoveryRootRound
open LocalBitMultitape RecoveryExecution RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def candidateWord (lo hi : Bool) (s : Store) (i : Fin 4) : List Bool :=
  RecoveryRootCandidates.words lo hi s.root s.remainder i

def takeRootBit (lo hi : Bool) (s : Store) : Bool :=
  decide (value (candidateWord lo hi s 2) ≤ value (candidateWord lo hi s 3))

def Store.compared (s : Store) (lo hi : Bool) : Store :=
  {(s.candidates lo hi).clear with
    flag := takeRootBit lo hi s
    compareCapacity := max s.compareCapacity (2 * (s.root.length + 2) + 1)}

def differenceWord (lo hi : Bool) (s : Store) : List Bool :=
  SignedSortKey.binary (s.root.length + 2)
    (value (candidateWord lo hi s 3) - value (candidateWord lo hi s 2))

def Store.subtracted (s : Store) (lo hi : Bool) : Store :=
  {s.compared lo hi with
    difference := frame (differenceWord lo hi s)
    subtractCapacity := max s.subtractCapacity (2 * (s.root.length + 2) + 1)}

theorem word_length (lo hi : Bool) (s : Store) (hw : s.root.length = s.remainder.length) (i : Fin 4) :
    (candidateWord lo hi s i).length = s.root.length + 2 :=
  RecoveryRootCandidates.words_length lo hi s.root s.remainder hw i

theorem comparison_layout (lo hi : Bool) (s : Store) (hw : s.root.length = s.remainder.length) :
    ReadyRun (programs lo hi 2) (4 * (s.root.length + 2) + 4)
      (s.candidates lo hi).clear.tapes (s.compared lo hi).tapes := by
  have hw' : (candidateWord lo hi s 2).length = (candidateWord lo hi s 3).length := by
    rw [word_length lo hi s hw 2, word_length lo hi s hw 3]
  have h := (compare_ready (candidateWord lo hi s 2) (candidateWord lo hi s 3) s.compareCapacity hw').focus
    compareSlots compareSlots_injective (s.candidates lo hi).clear.tapes (by intro j; fin_cases j <;> rfl)
  rw [word_length lo hi s hw 2] at h
  have he : install compareSlots (s.candidates lo hi).clear.tapes
      ![frame (candidateWord lo hi s 2), frame (candidateWord lo hi s 3), [takeRootBit lo hi s],
        List.replicate (max s.compareCapacity (2 * (s.root.length + 2) + 1)) false] =
      (s.compared lo hi).tapes := by
    funext i
    fin_cases i
    · rw [install_other compareSlots _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other compareSlots _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other compareSlots _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other compareSlots _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · exact install_slot compareSlots compareSlots_injective _ _ 0
    · exact install_slot compareSlots compareSlots_injective _ _ 1
    · rw [install_other compareSlots _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · exact install_slot compareSlots compareSlots_injective _ _ 2
    · exact install_slot compareSlots compareSlots_injective _ _ 3
    · rw [install_other compareSlots _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other compareSlots _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other compareSlots _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other compareSlots _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
  simp only [takeRootBit] at he
  rw [he] at h
  exact h

theorem difference_ready (left right backing : List Bool) (capacity : Nat)
    (hw : left.length = right.length) (hba : value right ≤ value left)
    (hb : backing.length ≤ 2 * left.length + 1) :
    ReadyRun subtractMachine (4 * left.length + 4)
      ![frame left, frame right, backing, List.replicate capacity false]
      ![frame left, frame right, frame (SignedSortKey.binary left.length (value left - value right)),
        List.replicate (max capacity (2 * left.length + 1)) false] := by
  have hl := BoundedCounter.binary_of_value left
  have hr : SignedSortKey.binary left.length (value right) = right := by
    rw [hw]; exact BoundedCounter.binary_of_value right
  have h := subtract_ready left.length (value left) (value right) backing capacity hba (value_lt left) hb
  rw [hl, hr] at h
  exact h

theorem subtraction_layout (lo hi : Bool) (s : Store) (hw : s.root.length = s.remainder.length)
    (hflag : takeRootBit lo hi s = true) (hb : s.difference.length ≤ 2 * (s.root.length + 2) + 1) :
    ReadyRun (programs lo hi 3) (4 * (s.root.length + 2) + 4)
      (s.compared lo hi).tapes (s.subtracted lo hi).tapes := by
  have hw' : (candidateWord lo hi s 3).length = (candidateWord lo hi s 2).length := by
    rw [word_length lo hi s hw 3, word_length lo hi s hw 2]
  have hba : value (candidateWord lo hi s 2) ≤ value (candidateWord lo hi s 3) := by
    simpa [takeRootBit] using hflag
  have hb' : s.difference.length ≤ 2 * (candidateWord lo hi s 3).length + 1 := by
    rw [word_length lo hi s hw 3]; exact hb
  have h := (difference_ready (candidateWord lo hi s 3) (candidateWord lo hi s 2) s.difference
    s.subtractCapacity hw' hba hb').focus subtractSlots subtractSlots_injective (s.compared lo hi).tapes
      (by intro j; fin_cases j <;> rfl)
  rw [word_length lo hi s hw 3] at h
  have he : install subtractSlots (s.compared lo hi).tapes
      ![frame (candidateWord lo hi s 3), frame (candidateWord lo hi s 2), frame (differenceWord lo hi s),
        List.replicate (max s.subtractCapacity (2 * (s.root.length + 2) + 1)) false] =
      (s.subtracted lo hi).tapes := by
    funext i
    fin_cases i
    · rw [install_other subtractSlots _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other subtractSlots _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other subtractSlots _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other subtractSlots _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · exact install_slot subtractSlots subtractSlots_injective _ _ 1
    · exact install_slot subtractSlots subtractSlots_injective _ _ 0
    · rw [install_other subtractSlots _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other subtractSlots _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other subtractSlots _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · exact install_slot subtractSlots subtractSlots_injective _ _ 2
    · exact install_slot subtractSlots subtractSlots_injective _ _ 3
    · rw [install_other subtractSlots _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other subtractSlots _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
  simp only [differenceWord] at he
  rw [he] at h
  exact h

theorem compared_call (lo hi : Bool) (s : Store) (hw : s.root.length = s.remainder.length) :
    Timed (roundMachine lo hi) (4 * (s.root.length + 2) + 5)
      (controlConfig (RecoveryCalls.code sizes 2)
        (initialConfiguration (programs lo hi 2) (s.candidates lo hi).clear.tapes))
      (controlConfig (RecoveryCalls.code sizes (if takeRootBit lo hi s then 3 else 5))
        (initialConfiguration (programs lo hi (if takeRootBit lo hi s then 3 else 5)) (s.compared lo hi).tapes)) := by
  have h := (comparison_layout lo hi s hw).call sizes (programs lo hi) 0 next 2
    (if takeRootBit lo hi s then 3 else 5)
    (by intro q; cases hf : takeRootBit lo hi s <;> simp [next, Store.tapes, Store.compared, readTapeBit, List.getD, hf])
  exact h

end NearCubicWires.RepairOrdinary.RecoveryRootRound
