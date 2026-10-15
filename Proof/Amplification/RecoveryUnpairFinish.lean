import Proof.Amplification.RecoveryUnpairFinishTapes

/-! The final unpair split is an actual finite controller, with both branches
executed through their copies and charged tape resets. -/
namespace NearCubicWires.RepairOrdinary.RecoveryUnpairFinish
open LocalBitMultitape RecoveryExecution RadixSemantics RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes : Fin 7 → Nat := ![2, 7, 7, 6, 6, 6, 6]
noncomputable def programs : (j : Fin 7) → Machine 13 (sizes j)
  | ⟨0, _⟩ => RecoveryFocus.machine clearSlots clearMachine
  | ⟨1, _⟩ => RecoveryFocus.machine compareSlots compareMachine
  | ⟨2, _⟩ => RecoveryFocus.machine subtractSlots subtractMachine
  | ⟨3, _⟩ => RecoveryFocus.machine differenceCopySlots copyMachine
  | ⟨4, _⟩ => RecoveryFocus.machine rootCopySlots copyMachine
  | ⟨5, _⟩ => RecoveryFocus.machine remainderCopySlots copyMachine
  | ⟨6, _⟩ => RecoveryFocus.machine differenceCopySlots copyMachine
  | ⟨n + 7, h⟩ => False.elim (by omega)

def next (j : Fin 7) (_ : Fin (sizes j)) (scanned : Fin 13 → Bool) : Option (Fin 7) :=
  if j.val = 0 then some 1
  else if j.val = 1 then if scanned 7 then some 2 else some 4
  else if j.val = 2 then some 3
  else if j.val = 4 then some 5
  else if j.val = 5 then some 6
  else none

noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

def finished (s : Store) : Store :=
  if branch s then differenceCopied (subtracted (compared s)) (differenceWord s)
  else differenceCopied (remainderCopied (rootCopied (compared s))) s.root

def time (s : Store) : Nat :=
  if branch s then 16 * s.root.length + 21 else 28 * s.root.length + 34

theorem time_bound (s : Store) : time s ≤ 28 * s.root.length + 34 := by
  unfold time
  split <;> omega

theorem finish_ready (s : Store) (hw : s.root.length = s.remainder.length)
    (hb : s.difference.length ≤ 2 * s.root.length + 1) :
    ReadyRun machine (time s) s.tapes (finished s).tapes := by
  have hc := (clear_layout false false s).call sizes programs 0 next 0 1 (by intro q; rfl)
  have hp := (compare_layout s hw).call sizes programs 0 next 1 (if branch s then 2 else 4)
    (by intro q; cases hf : branch s <;> simp [next, Store.tapes, compared, readTapeBit, List.getD, hf])
  have hstart := hc.trans hp
  have hin : controlConfig (RecoveryCalls.code sizes 0) (initialConfiguration (programs 0) s.tapes) =
      initialConfiguration machine s.tapes := by rfl
  rw [hin] at hstart
  have hpath : Timed machine (time s) (initialConfiguration machine s.tapes)
      (RecoveryCalls.stopped sizes (fun _ => 0) (finished s).tapes) := by
    cases hflag : branch s
    · rw [hflag] at hstart
      have ha := (root_copy_layout (compared s) hb).call sizes programs 0 next 4 5 (by intro q; rfl)
      have hb' := (remainder_copy_layout (rootCopied (compared s)) hw).call
        sizes programs 0 next 5 6 (by intro q; rfl)
      have hd := (difference_copy_layout (remainderCopied (rootCopied (compared s))) s.root
        rfl hw.symm).stop sizes programs 0 next 6 (by intro q; rfl)
      have h := ((hstart.trans ha).trans hb').trans hd
      change Timed machine (((1 + 1 + (4 * s.root.length + 4 + 1)) +
          (8 * s.root.length + 8 + 1)) + (8 * s.remainder.length + 8 + 1) +
          (8 * s.root.length + 8 + 1)) _ _ at h
      rw [← hw] at h
      have he : ((1 + 1 + (4 * s.root.length + 4 + 1)) + (8 * s.root.length + 8 + 1)) +
          (8 * s.root.length + 8 + 1) + (8 * s.root.length + 8 + 1) = 28 * s.root.length + 34 := by omega
      rw [he] at h
      simpa only [time, finished, hflag, Bool.false_eq_true, ↓reduceIte] using h
    · rw [hflag] at hstart
      have hba : value s.root ≤ value s.remainder := by simpa [branch] using hflag
      have ha := (subtract_layout (compared s) hw hba hb).call sizes programs 0 next 2 3
        (by intro q; rfl)
      have hwidth : (subtracted (compared s)).remainder.length = (differenceWord s).length := by
        simpa [subtracted, compared, differenceWord] using hw.symm
      have hd := (difference_copy_layout (subtracted (compared s)) (differenceWord s)
        rfl hwidth).stop sizes programs 0 next 3 (by intro q; rfl)
      have h := (hstart.trans ha).trans hd
      change Timed machine ((1 + 1 + (4 * s.root.length + 4 + 1) +
          (4 * s.root.length + 4 + 1)) + (8 * (differenceWord s).length + 8 + 1)) _ _ at h
      have hdlen : (differenceWord s).length = s.root.length := by simp [differenceWord]
      rw [hdlen] at h
      have he : (1 + 1 + (4 * s.root.length + 4 + 1) + (4 * s.root.length + 4 + 1)) +
          (8 * s.root.length + 8 + 1) = 16 * s.root.length + 21 := by omega
      rw [he] at h
      simpa only [time, finished, hflag, ↓reduceIte] using h
  obtain ⟨r, hr, hf, hs⟩ := hpath.run
    (by simp [machine, RecoveryCalls.machine, RecoveryCalls.stopped])
  exact ⟨r, hr, by simp [hf, RecoveryCalls.stopped],
    by intro i; simp [hf, RecoveryCalls.stopped], hs⟩

theorem difference_value (s : Store) (hw : s.root.length = s.remainder.length) :
    value (differenceWord s) = value s.remainder - value s.root := by
  apply SignedSortKey.binary_value
  have hv := value_lt s.remainder
  rw [← hw] at hv
  exact (Nat.sub_le _ _).trans_lt hv

theorem finished_values (s : Store) (hw : s.root.length = s.remainder.length) :
    (value (finished s).root, value (finished s).remainder) =
      RepairSource.RecoveryOracle.RestoringRoot.finish s.numeric := by
  cases hf : branch s
  · have hlt : value s.remainder < value s.root := by
      have hn : ¬value s.root ≤ value s.remainder := by simpa [branch] using hf
      omega
    simp [finished, hf, differenceCopied, remainderCopied, rootCopied, compared,
      RepairSource.RecoveryOracle.RestoringRoot.finish, Store.numeric, hlt]
  · have hge : value s.root ≤ value s.remainder := by simpa [branch] using hf
    have hn : ¬value s.remainder < value s.root := by omega
    simp [finished, hf, differenceCopied, subtracted, compared,
      RepairSource.RecoveryOracle.RestoringRoot.finish, Store.numeric, hn, difference_value s hw]

theorem finished_width (s : Store) (hw : s.root.length = s.remainder.length) :
    (finished s).root.length = s.root.length ∧ (finished s).remainder.length = s.root.length := by
  cases hf : branch s <;>
    simp [finished, hf, differenceCopied, remainderCopied, rootCopied, compared, subtracted, differenceWord, hw]

end NearCubicWires.RepairOrdinary.RecoveryUnpairFinish
