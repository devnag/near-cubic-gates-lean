import Proof.Amplification.RecoveryRootCopies

/-! One complete restoring-square-root digit is now an actual ordinary run.
Both comparison outcomes execute through their selected copies and halt. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRootRound
open LocalBitMultitape RecoveryExecution RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def roundTime (lo hi : Bool) (s : Store) : Nat :=
  if takeRootBit lo hi s then 28 * s.root.length + 95 else 24 * s.root.length + 82

theorem round_time_le (lo hi : Bool) (s : Store) : roundTime lo hi s ≤ 28 * s.root.length + 95 := by
  unfold roundTime
  split <;> omega

theorem round_ready (lo hi : Bool) (s : Store) (hw : s.root.length = s.remainder.length)
    (hb : ∀ i : Fin 4, (![s.lowCandidate, s.highCandidate, s.trial, s.shifted] i).length ≤
      2 * (s.root.length + 2) + 1)
    (hdiff : s.difference.length ≤ 2 * (s.root.length + 2) + 1) :
    ReadyRun (roundMachine lo hi) (roundTime lo hi s) s.tapes
      (s.completed lo hi (takeRootBit lo hi s)).tapes := by
  have hfirst := candidates_clear_call lo hi s hw hb
  have hcompare := compared_call lo hi s hw
  have hstart := hfirst.trans hcompare
  have hpath : Timed (roundMachine lo hi) (roundTime lo hi s)
      (initialConfiguration (roundMachine lo hi) s.tapes)
      (RecoveryCalls.stopped sizes (fun _ => 0) (s.completed lo hi (takeRootBit lo hi s)).tapes) := by
    cases hflag : takeRootBit lo hi s
    · rw [hflag] at hstart
      have h := hstart.trans (copies_call lo hi false s hw)
      have he : (4 * s.root.length + 19 + (4 * (s.root.length + 2) + 5)) +
          (16 * (s.root.length + 2) + 18) = 24 * s.root.length + 82 := by omega
      rw [he] at h
      simpa [roundTime, hflag, Store.chosen] using h
    · rw [hflag] at hstart
      have hsub := (subtraction_layout lo hi s hw hflag hdiff).call sizes (programs lo hi) 0 next 3 4
        (by intro q; rfl)
      have h := (hstart.trans hsub).trans (copies_call lo hi true s hw)
      have he : ((4 * s.root.length + 19 + (4 * (s.root.length + 2) + 5)) +
          (4 * (s.root.length + 2) + 4 + 1)) + (16 * (s.root.length + 2) + 18) =
          28 * s.root.length + 95 := by omega
      rw [he] at h
      simpa [roundTime, hflag, Store.chosen] using h
  obtain ⟨r, hr, hf, hs⟩ := hpath.run
    (by simp [roundMachine, RecoveryCalls.machine, RecoveryCalls.stopped])
  exact ⟨r, hr, by simp [hf, RecoveryCalls.stopped],
    by intro i; simp [hf, RecoveryCalls.stopped], hs⟩

abbrev ArithmeticState := RepairSource.RecoveryOracle.RestoringRoot.State

def Store.numeric (s : Store) : ArithmeticState := ⟨value s.root, value s.remainder⟩

def digit (lo hi : Bool) : Fin 4 :=
  ⟨lo.toNat + 2 * hi.toNat, by cases lo <;> cases hi <;> decide⟩

theorem candidate_values (lo hi : Bool) (s : Store) :
    value (candidateWord lo hi s 0) = 2 * value s.root ∧
    value (candidateWord lo hi s 1) = 2 * value s.root + 1 ∧
    value (candidateWord lo hi s 2) = 4 * value s.root + 1 ∧
    value (candidateWord lo hi s 3) = 4 * value s.remainder + (digit lo hi).val := by
  simp [candidateWord, RecoveryRootCandidates.words, value, value_append, digit]
  omega

theorem differenceWord_value (lo hi : Bool) (s : Store) (hw : s.root.length = s.remainder.length) :
    value (differenceWord lo hi s) =
      value (candidateWord lo hi s 3) - value (candidateWord lo hi s 2) := by
  apply SignedSortKey.binary_value
  have hv := value_lt (candidateWord lo hi s 3)
  rw [word_length lo hi s hw 3] at hv
  exact (Nat.sub_le _ _).trans_lt hv

theorem completed_numeric (lo hi : Bool) (s : Store) (hw : s.root.length = s.remainder.length) :
    (s.completed lo hi (takeRootBit lo hi s)).numeric =
      RepairSource.RecoveryOracle.RestoringRoot.digitStep s.numeric (digit lo hi) := by
  obtain ⟨h0, h1, h2, h3⟩ := candidate_values lo hi s
  have hd := differenceWord_value lo hi s hw
  have hflag : takeRootBit lo hi s =
      decide (4 * value s.root + 1 ≤ 4 * value s.remainder + (digit lo hi).val) := by
    simp only [takeRootBit, h2, h3]
  rw [hflag]
  unfold RepairSource.RecoveryOracle.RestoringRoot.digitStep
  dsimp only [Store.numeric]
  split
  · next hlt =>
    have hn : ¬4 * value s.root + 1 ≤ 4 * value s.remainder + (digit lo hi).val := by omega
    simp [hn, Store.completed, Store.rootCopied, nextRootWord, nextRemainderWord, h0, h3]
  · next hge =>
    have hy : 4 * value s.root + 1 ≤ 4 * value s.remainder + (digit lo hi).val := by omega
    simp [hy, Store.completed, Store.rootCopied, nextRootWord, nextRemainderWord, h1, hd, h2, h3]

end NearCubicWires.RepairOrdinary.RecoveryRootRound
