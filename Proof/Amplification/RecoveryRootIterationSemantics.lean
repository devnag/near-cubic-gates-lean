import Proof.Amplification.RecoveryRootRound

/-! The iteration invariant used by the actual digit loop. Width grows by two
per round; all arithmetic backing and the time envelope follow that width. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRootIteration
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Digit := Bool × Bool

def Valid (s : Store) : Prop :=
  s.root.length = s.remainder.length ∧
  (∀ i : Fin 4, (![s.lowCandidate, s.highCandidate, s.trial, s.shifted] i).length ≤ 2 * s.root.length + 1) ∧
  s.difference.length ≤ 2 * s.root.length + 1

def advance (d : Digit) (s : Store) : Store := s.completed d.1 d.2 (takeRootBit d.1 d.2 s)

theorem advance_width (d : Digit) (s : Store) (h : Valid s) :
    (advance d s).root.length = s.root.length + 2 ∧
    (advance d s).remainder.length = s.root.length + 2 := by
  exact ⟨nextRootWord_length d.1 d.2 _ s h.1, nextRemainderWord_length d.1 d.2 _ s h.1⟩

theorem advance_valid (d : Digit) (s : Store) (h : Valid s) : Valid (advance d s) := by
  obtain ⟨hroot, hrem⟩ := advance_width d s h
  refine ⟨hroot.trans hrem.symm, ?_, ?_⟩
  · intro i
    rw [hroot]
    have hw := word_length d.1 d.2 s h.1 i
    have hf : (frame (candidateWord d.1 d.2 s i)).length ≤ 2 * (s.root.length + 2) + 1 := by
      rw [frame_length, hw]
    cases hb : takeRootBit d.1 d.2 s <;> fin_cases i <;>
      simpa [advance, hb, Store.completed, Store.rootCopied, Store.chosen, Store.compared,
        Store.subtracted, Store.clear, Store.candidates, candidateWord] using hf
  · rw [hroot]
    cases hb : takeRootBit d.1 d.2 s
    · have hd := h.2.2
      simpa [advance, hb, Store.completed, Store.rootCopied, Store.chosen, Store.compared,
        Store.clear, Store.candidates] using (show s.difference.length ≤ 2 * (s.root.length + 2) + 1 by omega)
    · simp [advance, hb, Store.completed, Store.rootCopied, Store.chosen, Store.subtracted,
        differenceWord]

theorem advance_ready (d : Digit) (s : Store) (h : Valid s) :
    ReadyRun (roundMachine d.1 d.2) (roundTime d.1 d.2 s) s.tapes (advance d s).tapes := by
  apply round_ready d.1 d.2 s h.1
  · intro i
    have hi := h.2.1 i
    omega
  · have hi := h.2.2
    omega

def iterate : List Digit → Store → Store
  | [], s => s
  | d :: ds, s => iterate ds (advance d s)

def time : List Digit → Store → Nat
  | [], _ => 2
  | d :: ds, s => roundTime d.1 d.2 s + 6 + time ds (advance d s)

theorem iterate_valid (ds : List Digit) (s : Store) (h : Valid s) : Valid (iterate ds s) := by
  induction ds generalizing s with
  | nil => exact h
  | cons d ds ih => exact ih _ (advance_valid d s h)

theorem iterate_width (ds : List Digit) (s : Store) (h : Valid s) :
    (iterate ds s).root.length = s.root.length + 2 * ds.length := by
  induction ds generalizing s with
  | nil => simp [iterate]
  | cons d ds ih =>
    have hh := advance_valid d s h
    have hw := (advance_width d s h).1
    simpa [iterate, hw, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (advance d s) hh

theorem iterate_numeric (ds : List Digit) (s : Store) (h : Valid s) :
    (iterate ds s).numeric = RepairSource.RecoveryOracle.RestoringRoot.execute
      (ds.map (fun d => digit d.1 d.2)) s.numeric := by
  induction ds generalizing s with
  | nil => rfl
  | cons d ds ih =>
    rw [iterate, ih _ (advance_valid d s h)]
    have he := completed_numeric d.1 d.2 s h.1
    exact congrArg (RepairSource.RecoveryOracle.RestoringRoot.execute (ds.map (fun d => digit d.1 d.2))) he

theorem time_bound (ds : List Digit) (s : Store) (h : Valid s) :
    time ds s ≤ ds.length * (28 * (s.root.length + 2 * ds.length) + 101) + 2 := by
  induction ds generalizing s with
  | nil => simp [time]
  | cons d ds ih =>
    have ht := ih _ (advance_valid d s h)
    have hr := round_time_le d.1 d.2 s
    have hw := (advance_width d s h).1
    rw [hw] at ht
    simp only [time, List.length_cons]
    nlinarith

theorem initial_time_bound (ds : List Digit) (s : Store) (h : Valid s) (hw : s.root.length = 3) :
    time ds s ≤ 256 * (ds.length + 1) ^ 2 := by
  have ht := time_bound ds s h
  rw [hw] at ht
  nlinarith

end NearCubicWires.RepairOrdinary.RecoveryRootIteration
