import Proof.Wire_3_5.UnionMachineCallRound

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution

variable {t s : ℕ}

/-- **The loop exits** when the condition bit is clear. -/
theorem whileF (M : Machine t s) (i : Fin t) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (hb : readTapeBit (A i) (H i) = false) : Step (StreamController.machine M i) 1 H A H A := by
  have hs := StreamController.stop_step M i ⟨M.start, H, A⟩ hb
  have hr := runFrom_step (fuel := 0) (StreamController.machine M i) _ _ _
    (StreamController.test_halted M i) hs (runFrom_zero_of_halted _ _ (StreamController.stop_halted _ _))
  exact ⟨_, hr, rfl, rfl, by simp⟩

/-- **One round of the loop** when the condition bit is set. -/
theorem whileT (M : Machine t s) (i : Fin t) {H H1 H2 : Fin t → ℕ} {A A1 A2 : Fin t → List Bool} {n k : ℕ}
    (hb : readTapeBit (A i) (H i) = true) (h1 : Step M n H A H1 A1)
    (h2 : Step (StreamController.machine M i) k H1 A1 H2 A2) :
    Step (StreamController.machine M i) (n + 2 + k) H A H2 A2 := by
  obtain ⟨r1, hr1, hh1, ht1, hs1⟩ := h1
  obtain ⟨r2, hr2, hh2, ht2, hs2⟩ := h2
  have henter := StreamController.enter_step M i ⟨M.start, H, A⟩ hb
  obtain ⟨hbody, hhalt⟩ := StreamController.body_prefix M i n _ r1 hr1
  have hret := StreamController.return_step M i r1.final hhalt
  have t1 := Timed.single (StreamController.test_halted M i) henter
  have t2 : Timed (StreamController.machine M i) r1.steps
      (controlConfig RecordController.code (Composition.restart ⟨M.start, H, A⟩ M.start))
      (controlConfig RecordController.code r1.final) := ⟨_, hbody⟩
  have t3 := Timed.single (StreamController.body_halted M i r1.final.control) hret
  have e3 : controlConfig (fun _ => RecordController.test s) r1.final =
      (⟨(StreamController.machine M i).start, H1, A1⟩ : Configuration t (s + 2)) := by
    apply configuration_ext
    · rfl
    · exact hh1
    · exact ht1
  rw [e3] at t3
  obtain ⟨sp, hpre⟩ := (t1.trans t2).trans t3
  obtain ⟨joined, hj, hjf, hjs, _⟩ := hpre.followedBy r2 hr2
  have e1 : controlConfig (fun _ => RecordController.test s) (⟨M.start, H, A⟩ : Configuration t s) =
      ⟨(StreamController.machine M i).start, H, A⟩ := rfl
  rw [e1] at hj
  have more := runFrom_moreFuel _ (1 + r1.steps + 1 + k) (n + 2 + k - (1 + r1.steps + 1 + k)) _ joined hj
  rw [show 1 + r1.steps + 1 + k + (n + 2 + k - (1 + r1.steps + 1 + k)) = n + 2 + k by omega] at more
  refine ⟨joined, more, ?_, ?_, by omega⟩
  · rw [hjf]; exact hh2
  · rw [hjf]; exact ht2

/-- **`n` rounds of the loop** along the banks `(Hs j, As j)`: the condition bit is set before rounds `0 … n−1`
and clear after the last; each round is one body `Step` within `c`. -/
theorem whileRun (M : Machine t s) (i : Fin t) (n c : ℕ) (Hs : ℕ → Fin t → ℕ) (As : ℕ → Fin t → List Bool)
    (hT : ∀ j < n, readTapeBit (As j i) (Hs j i) = true) (hF : readTapeBit (As n i) (Hs n i) = false)
    (hb : ∀ j < n, Step M c (Hs j) (As j) (Hs (j + 1)) (As (j + 1))) :
    Step (StreamController.machine M i) (n * (c + 2) + 1) (Hs 0) (As 0) (Hs n) (As n) := by
  have key : ∀ m j, j + m = n →
      Step (StreamController.machine M i) (m * (c + 2) + 1) (Hs j) (As j) (Hs n) (As n) := by
    intro m
    induction m with
    | zero =>
      intro j hj
      rw [Nat.add_zero] at hj; subst hj
      simpa using whileF M i (Hs j) (As j) hF
    | succ m ih =>
      intro j hj
      have h := whileT M i (hT j (by omega)) (hb j (by omega)) (ih (j + 1) (by omega))
      exact h.enlarge (by nlinarith)
  simpa using key n 0 (by omega)

end NearCubicWires.WireExponent3_5.UnionMachine
