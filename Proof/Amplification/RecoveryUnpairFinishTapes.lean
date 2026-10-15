import Proof.Amplification.RecoveryRootLoop

/-! Paid final comparison, subtraction, and swap layouts for ordinary unpair. -/
namespace NearCubicWires.RepairOrdinary.RecoveryUnpairFinish
open LocalBitMultitape RecoveryExecution RadixSemantics RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def compareSlots : Fin 4 → Fin 13 := ![0, 1, 7, 8]
def subtractSlots : Fin 4 → Fin 13 := ![1, 0, 9, 10]
def rootCopySlots : Fin 4 → Fin 13 := ![0, 9, 11, 12]
def remainderCopySlots : Fin 4 → Fin 13 := ![1, 0, 11, 12]
def differenceCopySlots : Fin 4 → Fin 13 := ![9, 1, 11, 12]
theorem compareSlots_injective : Function.Injective compareSlots := by decide
theorem subtractSlots_injective : Function.Injective subtractSlots := by decide
theorem rootCopySlots_injective : Function.Injective rootCopySlots := by decide
theorem remainderCopySlots_injective : Function.Injective remainderCopySlots := by decide
theorem differenceCopySlots_injective : Function.Injective differenceCopySlots := by decide

def branch (s : Store) : Bool := decide (value s.root ≤ value s.remainder)
def compared (s : Store) : Store := {s with
  flag := branch s
  compareCapacity := max s.compareCapacity (2 * s.root.length + 1)}
def differenceWord (s : Store) : List Bool :=
  SignedSortKey.binary s.root.length (value s.remainder - value s.root)
def subtracted (s : Store) : Store := {s with
  difference := frame (differenceWord s)
  subtractCapacity := max s.subtractCapacity (2 * s.root.length + 1)}
def rootCopied (s : Store) : Store := {s with
  difference := frame s.root
  copyCapacity := max s.copyCapacity (2 * s.root.length + 1)
  resetCapacity := max s.resetCapacity (4 * s.root.length + 3)}
def remainderCopied (s : Store) : Store := {s with
  root := s.remainder
  copyCapacity := max s.copyCapacity (2 * s.remainder.length + 1)
  resetCapacity := max s.resetCapacity (4 * s.remainder.length + 3)}
def differenceCopied (s : Store) (bits : List Bool) : Store := {s with
  remainder := bits
  copyCapacity := max s.copyCapacity (2 * bits.length + 1)
  resetCapacity := max s.resetCapacity (4 * bits.length + 3)}

theorem compare_layout (s : Store) (hw : s.root.length = s.remainder.length) :
    ReadyRun (RecoveryFocus.machine compareSlots compareMachine) (4 * s.root.length + 4)
      s.clear.tapes (compared s).tapes := by
  have h := (compare_ready s.root s.remainder s.compareCapacity hw).focus
    compareSlots compareSlots_injective s.clear.tapes (by intro j; fin_cases j <;> rfl)
  have he : install compareSlots s.clear.tapes
      ![frame s.root, frame s.remainder, [branch s],
        List.replicate (max s.compareCapacity (2 * s.root.length + 1)) false] =
      (compared s).tapes := by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot compareSlots compareSlots_injective _ _ 0
      | exact install_slot compareSlots compareSlots_injective _ _ 1
      | exact install_slot compareSlots compareSlots_injective _ _ 2
      | exact install_slot compareSlots compareSlots_injective _ _ 3
      | exact install_other compareSlots _ _ _ (by intro j; fin_cases j <;> decide)
  simp only [branch] at he
  rw [he] at h
  exact h

theorem subtract_layout (s : Store) (hw : s.root.length = s.remainder.length)
    (hba : value s.root ≤ value s.remainder)
    (hb : s.difference.length ≤ 2 * s.root.length + 1) :
    ReadyRun (RecoveryFocus.machine subtractSlots subtractMachine) (4 * s.root.length + 4)
      s.tapes (subtracted s).tapes := by
  have hb' : s.difference.length ≤ 2 * s.remainder.length + 1 := by omega
  have h := (difference_ready s.remainder s.root s.difference s.subtractCapacity hw.symm hba hb').focus
    subtractSlots subtractSlots_injective s.tapes (by intro j; fin_cases j <;> rfl)
  rw [← hw] at h
  have he : install subtractSlots s.tapes
      ![frame s.remainder, frame s.root, frame (differenceWord s),
        List.replicate (max s.subtractCapacity (2 * s.root.length + 1)) false] =
      (subtracted s).tapes := by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot subtractSlots subtractSlots_injective _ _ 0
      | exact install_slot subtractSlots subtractSlots_injective _ _ 1
      | exact install_slot subtractSlots subtractSlots_injective _ _ 2
      | exact install_slot subtractSlots subtractSlots_injective _ _ 3
      | exact install_other subtractSlots _ _ _ (by intro j; fin_cases j <;> decide)
  simp only [differenceWord] at he
  rw [he] at h
  exact h

theorem root_copy_layout (s : Store) (hb : s.difference.length ≤ 2 * s.root.length + 1) :
    ReadyRun (RecoveryFocus.machine rootCopySlots copyMachine) (8 * s.root.length + 8)
      s.tapes (rootCopied s).tapes := by
  have h := (copy_ready s.root s.difference s.copyCapacity s.resetCapacity hb).focus
    rootCopySlots rootCopySlots_injective s.tapes (by intro j; fin_cases j <;> rfl)
  have he : install rootCopySlots s.tapes
      ![frame s.root, frame s.root,
        List.replicate (max s.copyCapacity (2 * s.root.length + 1)) false,
        List.replicate (max s.resetCapacity (4 * s.root.length + 3)) false] =
      (rootCopied s).tapes := by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot rootCopySlots rootCopySlots_injective _ _ 0
      | exact install_slot rootCopySlots rootCopySlots_injective _ _ 1
      | exact install_slot rootCopySlots rootCopySlots_injective _ _ 2
      | exact install_slot rootCopySlots rootCopySlots_injective _ _ 3
      | exact install_other rootCopySlots _ _ _ (by intro j; fin_cases j <;> decide)
  rw [he] at h
  exact h

theorem remainder_copy_layout (s : Store) (hw : s.root.length = s.remainder.length) :
    ReadyRun (RecoveryFocus.machine remainderCopySlots copyMachine) (8 * s.remainder.length + 8)
      s.tapes (remainderCopied s).tapes := by
  have hb : (frame s.root).length ≤ 2 * s.remainder.length + 1 := by rw [frame_length, hw]
  have h := (copy_ready s.remainder (frame s.root) s.copyCapacity s.resetCapacity hb).focus
    remainderCopySlots remainderCopySlots_injective s.tapes (by intro j; fin_cases j <;> rfl)
  have he : install remainderCopySlots s.tapes
      ![frame s.remainder, frame s.remainder,
        List.replicate (max s.copyCapacity (2 * s.remainder.length + 1)) false,
        List.replicate (max s.resetCapacity (4 * s.remainder.length + 3)) false] =
      (remainderCopied s).tapes := by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot remainderCopySlots remainderCopySlots_injective _ _ 0
      | exact install_slot remainderCopySlots remainderCopySlots_injective _ _ 1
      | exact install_slot remainderCopySlots remainderCopySlots_injective _ _ 2
      | exact install_slot remainderCopySlots remainderCopySlots_injective _ _ 3
      | exact install_other remainderCopySlots _ _ _ (by intro j; fin_cases j <;> decide)
  rw [he] at h
  exact h

theorem difference_copy_layout (s : Store) (bits : List Bool)
    (hsource : s.difference = frame bits) (hw : s.remainder.length = bits.length) :
    ReadyRun (RecoveryFocus.machine differenceCopySlots copyMachine) (8 * bits.length + 8)
      s.tapes (differenceCopied s bits).tapes := by
  have hb : (frame s.remainder).length ≤ 2 * bits.length + 1 := by rw [frame_length, hw]
  have h := (copy_ready bits (frame s.remainder) s.copyCapacity s.resetCapacity hb).focus
    differenceCopySlots differenceCopySlots_injective s.tapes
      (by intro j; fin_cases j; exact hsource; all_goals rfl)
  have he : install differenceCopySlots s.tapes
      ![frame bits, frame bits,
        List.replicate (max s.copyCapacity (2 * bits.length + 1)) false,
        List.replicate (max s.resetCapacity (4 * bits.length + 3)) false] =
      (differenceCopied s bits).tapes := by
    funext i
    fin_cases i
    all_goals first
      | exact (install_slot differenceCopySlots differenceCopySlots_injective _ _ 0).trans hsource.symm
      | exact install_slot differenceCopySlots differenceCopySlots_injective _ _ 0
      | exact install_slot differenceCopySlots differenceCopySlots_injective _ _ 1
      | exact install_slot differenceCopySlots differenceCopySlots_injective _ _ 2
      | exact install_slot differenceCopySlots differenceCopySlots_injective _ _ 3
      | exact install_other differenceCopySlots _ _ _ (by intro j; fin_cases j <;> decide)
  rw [he] at h
  exact h

end NearCubicWires.RepairOrdinary.RecoveryUnpairFinish
