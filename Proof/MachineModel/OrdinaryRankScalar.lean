import Proof.MachineModel.OrdinaryRankWorkspace

/-! Scalar reset/increment at the rank scan's exact retained-workspace
boundary. These run on just the rank and scratch tapes, so an enclosing
embedding preserves the source and output append cursors. -/
namespace NearCubicWires.RepairOrdinary.RankScalar
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem runFrom_start {t s : ℕ} (p : Machine t s) (state : Fin s) (fuel : ℕ)
    (c : Configuration t s) :
    runFrom { p with start := state } fuel c = runFrom p fuel c := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
    simp only [runFrom]
    split
    · rfl
    · simp only [step]
      split
      · rfl
      · simp only [ih]

def reset : Machine 2 4 := { Rewind.machine BinaryIncrement.machine with start := 2 }

def scalarConfig (state : Fin 4) (rank : List Bool) (rankHead : ℕ)
    (scratch : List Bool) (scratchHead : ℕ) : Configuration 2 4 :=
  ⟨state, fun i => if i.val = 0 then rankHead else scratchHead,
    fun i => if i.val = 0 then rank else scratch⟩

theorem reset_run (bits : List Bool) :
    ∃ r : ExecutionReceipt 2 4,
      runFrom reset (bits.length + 1)
        (scalarConfig 2 bits bits.length (List.replicate bits.length true) (bits.length - 1)) = some r ∧
      r.final = scalarConfig 3 bits 0 (List.replicate bits.length false) 0 ∧
      r.steps = bits.length + 1 ∧ r.peakTapeCells ≤ 2 * bits.length := by
  obtain ⟨r, hr, hf, hs, hp⟩ := Rewind.rewind_run BinaryIncrement.machine
    (fun _ : Fin 1 => bits.length) (fun _ : Fin 1 => bits) bits.length 0 (by simp)
  have hi : Rewind.rewinding (s := 2) (fun _ : Fin 1 => bits.length)
      (fun _ : Fin 1 => bits) bits.length 0 =
      scalarConfig 2 bits bits.length (List.replicate bits.length true) (bits.length - 1) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Rewind.rewinding, Rewind.config, scalarConfig, Fin.addCases]
    · funext i
      fin_cases i <;> simp [Rewind.rewinding, Rewind.config, scalarConfig, Fin.addCases]
  refine ⟨r, ?_, ?_, hs, ?_⟩
  · rw [reset, runFrom_start, ← hi]
    exact hr
  · rw [hf]
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Rewind.finished, Rewind.config, scalarConfig, Fin.addCases]
    · funext i
      fin_cases i <;> simp [Rewind.finished, Rewind.config, scalarConfig, Fin.addCases]
  · simpa [Rewind.tapeCells, two_mul] using hp

def capacity (width : ℕ) : Fin 2 → ℕ := fun i => if i.val = 1 then width else 0

theorem increment_run (width n : ℕ) (hn : n + 1 < 2 ^ width) :
    ∃ r : ExecutionReceipt 2 4,
      runFrom (Rewind.machine BinaryIncrement.machine) (2 * width + 2)
        (scalarConfig 0 (SignedSortKey.binary width n) 0 (List.replicate width false) 0) = some r ∧
      r.final = scalarConfig 3 (SignedSortKey.binary width (n + 1)) 0 (List.replicate width false) 0 ∧
      r.steps ≤ 2 * width + 2 ∧ r.peakTapeCells ≤ 4 * width := by
  obtain ⟨next, base, hnxt, hb, hbits, hscratch, hheads, hs, hp⟩ :=
    BoundedCounter.increment_run width n 0 hn (Nat.zero_le _)
  have hhalt := (prefix_of_run (Rewind.machine BinaryIncrement.machine) (2 * width + 2) _ base hb).2
  have hctl : base.final.control = 3 := by
    have ht : ∀ state : Fin 4, (Rewind.machine BinaryIncrement.machine).halted state = true → state = 3 := by
      intro state
      fin_cases state <;> simp [Rewind.machine, Fin.addCases]
    exact ht _ hhalt
  obtain ⟨r, hr, hf, hrs, hrp⟩ := ZeroPadding.run_config (Rewind.machine BinaryIncrement.machine)
    (capacity width) (2 * width + 2) _ base hb
  have hi : ZeroPadding.config (capacity width)
      (initialConfiguration (Rewind.machine BinaryIncrement.machine)
        (Fin.addCases (motive := fun _ : Fin (1 + 1) => List Bool)
          (fun _ : Fin 1 => SignedSortKey.binary width n)
          (fun _ : Fin 1 => List.replicate 0 false))) =
      scalarConfig 0 (SignedSortKey.binary width n) 0 (List.replicate width false) 0 := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config, capacity, initialConfiguration, scalarConfig,
        Fin.addCases, ZeroPadding.pad]
  refine ⟨r, by rw [hi] at hr; exact hr, ?_, hrs.le.trans hs, ?_⟩
  · rw [hf]
    apply configuration_ext
    · exact hctl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config, scalarConfig, hheads]
    · funext i
      fin_cases i
      · simp [ZeroPadding.config, capacity, hbits, scalarConfig]
      · simp [ZeroPadding.config, capacity, hscratch, scalarConfig, Rewind.Workspace.pad_zeros,
          max_eq_left hnxt]
  · have hc : ZeroPadding.cells (capacity width) = width := by
      simp [ZeroPadding.cells, capacity, Fin.sum_univ_succ]
    rw [hc] at hrp
    omega

end NearCubicWires.RepairOrdinary.RankScalar
