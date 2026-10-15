import Proof.Amplification.RecoveryTapeSupport

/-! A reusable unary driver pays for a coarse sweep of arbitrary scratch.
Every selected cell is physically overwritten; all heads are then reset by
an executed rewind. The driver is preserved for subsequent scalar calls. -/
namespace NearCubicWires.RepairOrdinary.RecoveryScratchErase
open LocalBitMultitape RecoveryExecution RecoveryRootRound StablePartition.Workspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine (t : Nat) : Machine (t + 1) 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q scanned => if q.val = 0 then
    if scanned ((0 : Fin 1).natAdd t) then some ⟨0,
      Fin.addCases (fun _ : Fin t => some false) (fun _ : Fin 1 => none), fun _ => .right⟩
    else some ⟨1, fun _ => none, fun _ => .stay⟩
  else none

def tapes {t : Nat} (total done : Nat) (backing : Fin t → List Bool) : Fin (t + 1) → List Bool :=
  Fin.addCases (fun i => overlay (List.replicate done false) (backing i))
    (fun _ : Fin 1 => List.replicate total true)

def config {t : Nat} (q : Fin 2) (total done : Nat) (backing : Fin t → List Bool) : Configuration (t + 1) 2 :=
  ⟨q, fun _ => done, tapes total done backing⟩

theorem sweep_step {t : Nat} (total done : Nat) (backing : Fin t → List Bool) (hd : done < total) :
    step (machine t) (config 0 total done backing) = some (config 0 total (done + 1) backing) := by
  have hread : readTapeBit (List.replicate total true) done = true := by
    simp [readTapeBit, List.getD, hd]
  simp only [step, machine, config, Configuration.scanned, tapes, Fin.addCases_right, hread,
    Fin.val_zero, ↓reduceIte]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; rfl
  · funext i
    refine Fin.addCases (m := t) (n := 1) (motive := fun j =>
      (applyAction (config 0 total done backing)
        (⟨0,Fin.addCases (fun _ : Fin t => some false) (fun _ : Fin 1 => none),fun _ => .right⟩ : Action (t+1) 2)).tapes j =
          (config 0 total (done+1) backing).tapes j) ?_ ?_ i
    · intro j
      simp only [applyAction, config, tapes, Fin.addCases_left]
      have h := overlay_write (List.replicate done false) (backing j) false
      simpa only [List.length_replicate, List.replicate_add, List.replicate_one] using h
    · intro j
      simp [applyAction, config, tapes]

theorem stop_step {t : Nat} (total : Nat) (backing : Fin t → List Bool) :
    step (machine t) (config 0 total total backing) = some (config 1 total total backing) := by
  have hread : readTapeBit (List.replicate total true) total = false := by
    simp [readTapeBit, List.getD]
  simp only [step, machine, config, Configuration.scanned, tapes, Fin.addCases_right, hread,
    Fin.val_zero, ↓reduceIte]
  rfl

theorem sweep_prefix {t : Nat} (remaining done : Nat) (backing : Fin t → List Bool) :
    Timed (machine t) (remaining + 1) (config 0 (done + remaining) done backing)
      (config 1 (done + remaining) (done + remaining) backing) := by
  induction remaining generalizing done with
  | zero => simpa using Timed.single (by rfl) (stop_step done backing)
  | succ remaining ih =>
    have ht := ih (done + 1)
    have he : done + 1 + remaining = done + (remaining + 1) := by omega
    rw [he] at ht
    exact Timed.step (by rfl) (sweep_step (done + (remaining + 1)) done backing (by omega)) ht

theorem raw_run {t : Nat} (total : Nat) (backing : Fin t → List Bool)
    (hb : ∀ i, (backing i).length ≤ total) :
    ∃ r : ExecutionReceipt (t + 1) 2,
      run (machine t) (total + 1)
        (Fin.addCases backing (fun _ : Fin 1 => List.replicate total true)) = some r ∧
      r.final.tapes = Fin.addCases (fun _ : Fin t => List.replicate total false)
        (fun _ : Fin 1 => List.replicate total true) ∧ r.steps = total + 1 := by
  have h := sweep_prefix total 0 backing
  obtain ⟨r, hr, hf, hs⟩ := h.run (by rfl)
  have hi : config 0 (0 + total) 0 backing = initialConfiguration (machine t)
      (Fin.addCases backing (fun _ : Fin 1 => List.replicate total true)) := by
    apply configuration_ext
    · rfl
    · rfl
    · change tapes (0+total) 0 backing = _
      unfold RecoveryScratchErase.tapes initialConfiguration
      simp [overlay]
  rw [hi] at hr
  refine ⟨r, hr, ?_, hs⟩
  rw [hf]
  funext i
  refine Fin.addCases (m := t) (n := 1) (motive := fun j =>
    (config 1 (0+total) (0+total) backing).tapes j =
      Fin.addCases (fun _ : Fin t => List.replicate total false)
        (fun _ : Fin 1 => List.replicate total true) j) ?_ ?_ i
  · intro j
    simp [config, tapes, overlay, List.drop_eq_nil_of_le (hb j)]
  · intro j
    simp [config, tapes]

def resetMachine (t : Nat) : Machine (t + 1 + 1) 4 := Rewind.machine (machine t)

theorem erase_ready {t : Nat} (total capacity : Nat) (backing : Fin t → List Bool)
    (hb : ∀ i, (backing i).length ≤ total) :
    ReadyRun (resetMachine t) (2 * total + 4)
      (Fin.addCases (Fin.addCases backing (fun _ : Fin 1 => List.replicate total true))
        (fun _ : Fin 1 => List.replicate capacity false))
      (Fin.addCases (Fin.addCases (fun _ : Fin t => List.replicate total false)
        (fun _ : Fin 1 => List.replicate total true))
        (fun _ : Fin 1 => List.replicate (max capacity (total + 1)) false)) := by
  obtain ⟨source, hr, ht, hs⟩ := raw_run total backing hb
  obtain ⟨r, hrun, hbase, hc, hh, hsteps, _⟩ := Rewind.Workspace.reset_workspace
    (machine t) _ _ source hr capacity
  have he : 2 * source.steps + 2 = 2 * total + 4 := by rw [hs]; omega
  rw [he] at hrun
  refine ⟨r, hrun, ?_, hh, hsteps.trans he⟩
  funext i
  refine Fin.addCases (m := t+1) (n := 1) (motive := fun j =>
    r.final.tapes j = Fin.addCases
      (Fin.addCases (fun _ : Fin t => List.replicate total false) (fun _ : Fin 1 => List.replicate total true))
      (fun _ : Fin 1 => List.replicate (max capacity (total+1)) false) j) ?_ ?_ i
  · intro j
    simpa only [Fin.addCases_left, ht] using hbase j
  · intro j
    fin_cases j
    simp only [Fin.addCases_right]
    change r.final.tapes (Fin.natAdd (t+1) (0 : Fin 1)) = List.replicate (max capacity (total+1)) false
    simpa only [hs] using hc

end NearCubicWires.RepairOrdinary.RecoveryScratchErase
