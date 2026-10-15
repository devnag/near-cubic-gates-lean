import Proof.Amplification.RecoveryRootBranch

namespace NearCubicWires.RepairOrdinary.RecoveryRootRound
open LocalBitMultitape RecoveryExecution RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Store.chosen (s : Store) (lo hi branch : Bool) : Store :=
  if branch then s.subtracted lo hi else s.compared lo hi

def nextRootWord (lo hi branch : Bool) (s : Store) : List Bool :=
  candidateWord lo hi s (if branch then 1 else 0)

def nextRemainderWord (lo hi branch : Bool) (s : Store) : List Bool :=
  if branch then differenceWord lo hi s else candidateWord lo hi s 3

def Store.rootCopied (s : Store) (lo hi branch : Bool) : Store :=
  {s.chosen lo hi branch with
    root := nextRootWord lo hi branch s
    copyCapacity := max s.copyCapacity (2 * (s.root.length + 2) + 1)
    resetCapacity := max s.resetCapacity (4 * (s.root.length + 2) + 3)}

def Store.completed (s : Store) (lo hi branch : Bool) : Store :=
  {(s.rootCopied lo hi branch) with
    remainder := nextRemainderWord lo hi branch s
    copyCapacity := max (s.rootCopied lo hi branch).copyCapacity (2 * (s.root.length + 2) + 1)
    resetCapacity := max (s.rootCopied lo hi branch).resetCapacity (4 * (s.root.length + 2) + 3)}

theorem nextRootWord_length (lo hi branch : Bool) (s : Store)
    (hw : s.root.length = s.remainder.length) :
    (nextRootWord lo hi branch s).length = s.root.length + 2 := word_length lo hi s hw _

theorem nextRemainderWord_length (lo hi branch : Bool) (s : Store)
    (hw : s.root.length = s.remainder.length) :
    (nextRemainderWord lo hi branch s).length = s.root.length + 2 := by
  cases branch
  · exact word_length lo hi s hw 3
  · simp [nextRemainderWord, differenceWord]

theorem root_copy_layout (lo hi branch : Bool) (s : Store) (hw : s.root.length = s.remainder.length) :
    ReadyRun (programs lo hi (if branch then 4 else 5)) (8 * (s.root.length + 2) + 8)
      (s.chosen lo hi branch).tapes (s.rootCopied lo hi branch).tapes := by
  let slot := if branch then highCopySlots else lowCopySlots
  have hiSlot : Function.Injective slot := by
    cases branch
    · exact lowCopySlots_injective
    · exact highCopySlots_injective
  have hb : (frame s.root).length ≤ 2 * (nextRootWord lo hi branch s).length + 1 := by
    rw [frame_length, nextRootWord_length lo hi branch s hw]; omega
  have h := (copy_ready (nextRootWord lo hi branch s) (frame s.root) s.copyCapacity s.resetCapacity hb).focus
    slot hiSlot (s.chosen lo hi branch).tapes (by intro j; cases branch <;> fin_cases j <;> rfl)
  rw [nextRootWord_length lo hi branch s hw] at h
  have he : install slot (s.chosen lo hi branch).tapes
      ![frame (nextRootWord lo hi branch s), frame (nextRootWord lo hi branch s),
        List.replicate (max s.copyCapacity (2 * (s.root.length + 2) + 1)) false,
        List.replicate (max s.resetCapacity (4 * (s.root.length + 2) + 3)) false] =
      (s.rootCopied lo hi branch).tapes := by
    funext i
    cases branch <;> fin_cases i
    · exact install_slot slot hiSlot _ _ 1
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · exact install_slot slot hiSlot _ _ 0
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · exact install_slot slot hiSlot _ _ 2
    · exact install_slot slot hiSlot _ _ 3
    · exact install_slot slot hiSlot _ _ 1
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · exact install_slot slot hiSlot _ _ 0
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · exact install_slot slot hiSlot _ _ 2
    · exact install_slot slot hiSlot _ _ 3
  rw [he] at h
  cases branch <;> exact h

theorem remainder_copy_layout (lo hi branch : Bool) (s : Store) (hw : s.root.length = s.remainder.length) :
    ReadyRun (programs lo hi (if branch then 6 else 7)) (8 * (s.root.length + 2) + 8)
      (s.rootCopied lo hi branch).tapes (s.completed lo hi branch).tapes := by
  let slot := if branch then differenceCopySlots else shiftedCopySlots
  have hiSlot : Function.Injective slot := by
    cases branch
    · exact shiftedCopySlots_injective
    · exact differenceCopySlots_injective
  have hb : (frame s.remainder).length ≤ 2 * (nextRemainderWord lo hi branch s).length + 1 := by
    rw [frame_length, nextRemainderWord_length lo hi branch s hw]; omega
  have h := (copy_ready (nextRemainderWord lo hi branch s) (frame s.remainder)
    (s.rootCopied lo hi branch).copyCapacity (s.rootCopied lo hi branch).resetCapacity hb).focus
    slot hiSlot (s.rootCopied lo hi branch).tapes (by intro j; cases branch <;> fin_cases j <;> rfl)
  rw [nextRemainderWord_length lo hi branch s hw] at h
  have he : install slot (s.rootCopied lo hi branch).tapes
      ![frame (nextRemainderWord lo hi branch s), frame (nextRemainderWord lo hi branch s),
        List.replicate (max (s.rootCopied lo hi branch).copyCapacity (2 * (s.root.length + 2) + 1)) false,
        List.replicate (max (s.rootCopied lo hi branch).resetCapacity (4 * (s.root.length + 2) + 3)) false] =
      (s.completed lo hi branch).tapes := by
    funext i
    cases branch <;> fin_cases i
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · exact install_slot slot hiSlot _ _ 1
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · exact install_slot slot hiSlot _ _ 0
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · exact install_slot slot hiSlot _ _ 2
    · exact install_slot slot hiSlot _ _ 3
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · exact install_slot slot hiSlot _ _ 1
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · exact install_slot slot hiSlot _ _ 0
    · rw [install_other slot _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · exact install_slot slot hiSlot _ _ 2
    · exact install_slot slot hiSlot _ _ 3
  rw [he] at h
  cases branch <;> exact h

theorem copies_call (lo hi branch : Bool) (s : Store) (hw : s.root.length = s.remainder.length) :
    Timed (roundMachine lo hi) (16 * (s.root.length + 2) + 18)
      (controlConfig (RecoveryCalls.code sizes (if branch then 4 else 5))
        (initialConfiguration (programs lo hi (if branch then 4 else 5)) (s.chosen lo hi branch).tapes))
      (RecoveryCalls.stopped sizes (fun _ => 0) (s.completed lo hi branch).tapes) := by
  have ha := (root_copy_layout lo hi branch s hw).call sizes (programs lo hi) 0 next
    (if branch then 4 else 5) (if branch then 6 else 7) (by intro q; cases branch <;> rfl)
  have hb := (remainder_copy_layout lo hi branch s hw).stop sizes (programs lo hi) 0 next
    (if branch then 6 else 7) (by intro q; cases branch <;> rfl)
  have h := ha.trans hb
  have he : (8 * (s.root.length + 2) + 8 + 1) + (8 * (s.root.length + 2) + 8 + 1) =
      16 * (s.root.length + 2) + 18 := by omega
  rw [he] at h
  exact h

end NearCubicWires.RepairOrdinary.RecoveryRootRound
