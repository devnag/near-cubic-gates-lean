import Proof.MachineModel.OrdinaryPaperMatrix

/-! Paid reset of one designated source cursor after an actual program.
Every other head, including a growing output cursor, retains its endpoint. -/
namespace NearCubicWires.RepairOrdinary.SelectiveReset
open LocalBitMultitape
open Rewind (config recording rewinding tapeCells recordAction bridgeAction finishAction)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rewindAction {t : ℕ} (s : ℕ) (target : Fin t) : Action (t + 1) (s + 2) where
  nextControl := (0 : Fin 2).natAdd s
  write := Fin.addCases (fun _ => none) (fun _ => some false)
  move := Fin.addCases (fun i => if i = target then .left else .stay) (fun _ => .left)
def machine {t s : ℕ} (p : Machine t s) (target : Fin t) : Machine (t + 1) (s + 2) where
  descriptionBits := 0
  start := p.start.castAdd 2
  halted := (Rewind.machine p).halted
  rule := fun state scanned => Fin.addCases
    (fun c => if p.halted c then some (bridgeAction t s)
      else (p.rule c (fun i => scanned (i.castAdd 1))).map recordAction)
    (fun k => if k.val = 0 then
      if scanned ((0 : Fin 1).natAdd t) then some (rewindAction s target)
      else some (finishAction t s) else none) state

def finished {t s : ℕ} (heads : Fin t → ℕ) (tapes : Fin t → List Bool) (n : ℕ) : Configuration (t + 1) (s + 2) :=
  config ((1 : Fin 2).natAdd s) heads tapes 0 (List.replicate n false)

theorem record_step {t s : ℕ} (p : Machine t s) (target : Fin t) (c d : Configuration t s) (n : ℕ)
    (hn : p.halted c.control = false) (hs : step p c = some d) :
    step (machine p target) (recording c n) = some (recording d (n + 1)) := by
  have h := Rewind.record_step p c d n hn hs
  simpa only [step, machine, Rewind.machine, recording, config, Fin.addCases_left] using h

theorem bridge_step {t s : ℕ} (p : Machine t s) (target : Fin t) (c : Configuration t s) (n : ℕ)
    (hh : p.halted c.control = true) :
    step (machine p target) (recording c n) = some (rewinding (s := s) c.heads c.tapes n 0) := by
  have h := Rewind.bridge_step p c n hh
  simpa only [step, machine, Rewind.machine, recording, config, Fin.addCases_left] using h

theorem rewind_step {t s : ℕ} (p : Machine t s) (target : Fin t) (heads : Fin t → ℕ)
    (tapes : Fin t → List Bool) (n z : ℕ) :
    step (machine p target) (rewinding (s := s) heads tapes (n + 1) z) =
      some (rewinding (s := s) (fun i => if i = target then heads i - 1 else heads i) tapes n (z + 1)) := by
  have hr := Streaming.read_counter n z
  simp [step, machine, rewinding, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · by_cases h : j = target <;> simp [applyAction, rewindAction, HeadMove.apply, h]
    · simp [applyAction, rewindAction, HeadMove.apply]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [applyAction, rewindAction, Streaming.erase_counter]

theorem finish_step {t s : ℕ} (p : Machine t s) (target : Fin t) (heads : Fin t → ℕ)
    (tapes : Fin t → List Bool) (z : ℕ) :
    step (machine p target) (rewinding (s := s) heads tapes 0 z) = some (finished (s := s) heads tapes z) := by
  simp [step, machine, rewinding, config, Configuration.scanned, Streaming.read_zeros]
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [applyAction, finishAction, finished, config, HeadMove.apply]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [applyAction, finishAction, finished, config]

theorem rewind_prefix {t s : ℕ} (p : Machine t s) (target : Fin t) (heads : Fin t → ℕ)
    (tapes : Fin t → List Bool) (n z : ℕ) :
    Prefix (machine p target) (tapeCells tapes + n + z) (n + 1)
      (rewinding (s := s) heads tapes n z)
      (finished (s := s) (fun i => if i = target then heads i - n else heads i) tapes (n + z)) := by
  induction n generalizing heads z with
  | zero =>
    simpa using Prefix.step
      (by simp [rewinding] : (rewinding (s := s) heads tapes 0 z).tapeCells ≤ tapeCells tapes + z)
      (by simp [machine, Rewind.machine, rewinding, config]) (finish_step p target heads tapes z)
      (Prefix.refl _ (by simp [finished]))
  | succ n ih =>
    let next := fun i => if i = target then heads i - 1 else heads i
    have ht := ih next (z + 1)
    have hend : (fun i => if i = target then next i - n else next i) =
        fun i => if i = target then heads i - (n + 1) else heads i := by
      funext i
      by_cases h : i = target <;> simp [next, h, Nat.sub_sub, Nat.add_comm 1 n]
    rw [hend] at ht
    have hj := Prefix.step
      (by simp [rewinding]; omega : (rewinding (s := s) heads tapes (n + 1) z).tapeCells ≤ tapeCells tapes + n + (z + 1))
      (by simp [machine, Rewind.machine, rewinding, config]) (rewind_step p target heads tapes n z) ht
    simpa only [Nat.add_assoc, Nat.add_comm 1 z] using hj

theorem recording_prefix {t s space n : ℕ} {p : Machine t s} {c d : Configuration t s}
    (hp : Prefix p space n c d) (target : Fin t) (count : ℕ) :
    Prefix (machine p target) (space + count + n) n (recording c count) (recording d (count + n)) := by
  induction hp generalizing count with
  | refl c hc =>
    exact Prefix.refl _ (by
      simp only [recording, Rewind.config_cells, List.length_replicate, Nat.add_zero]
      change c.tapeCells + count ≤ space + count
      omega)
  | @step n c d e hc hn hs _ ih =>
    have ht := ih (count + 1)
    have hj := Prefix.step
      (by
        simp only [recording, Rewind.config_cells, List.length_replicate]
        change c.tapeCells + count ≤ space + (count + 1) + n
        omega :
        (recording c count).tapeCells ≤ space + (count + 1) + n)
      (by simp [machine, Rewind.machine, recording, config]) (record_step p target c d count hn hs) ht
    simpa only [Nat.add_assoc, Nat.add_comm 1 n] using hj

theorem reset_run {t s : ℕ} (p : Machine t s) (target : Fin t) (fuel : ℕ)
    (c : Configuration t s) (source : ExecutionReceipt t s)
    (hr : runFrom p fuel c = some source) (hhead : source.final.heads target ≤ source.steps) :
    ∃ r : ExecutionReceipt (t + 1) (s + 2),
      runFrom (machine p target) (2 * source.steps + 2) (recording c 0) = some r ∧
      r.final = finished (s := s) (fun i => if i = target then 0 else source.final.heads i)
        source.final.tapes source.steps ∧
      r.steps = 2 * source.steps + 2 ∧ r.peakTapeCells ≤ source.peakTapeCells + source.steps := by
  obtain ⟨hp, hh⟩ := prefix_of_run p fuel c source hr
  have hc := SortMatrix.final_cells hp
  have recorded := recording_prefix hp target 0
  have reset := rewind_prefix p target source.final.heads source.final.tapes source.steps 0
  have hheads : (fun i => if i = target then source.final.heads i - source.steps else source.final.heads i) =
      fun i => if i = target then 0 else source.final.heads i := by
    funext i
    by_cases hi : i = target
    · subst i; simp [Nat.sub_eq_zero_of_le hhead]
    · simp [hi]
  rw [hheads] at reset
  have reset' := reset.enlarge (large := source.peakTapeCells + source.steps) (by
    change source.final.tapeCells + source.steps + 0 ≤ _
    omega)
  have bridge := Prefix.step
    (by
      simp only [recording, Rewind.config_cells, List.length_replicate]
      change source.final.tapeCells + source.steps ≤ _
      omega :
      (recording source.final source.steps).tapeCells ≤ source.peakTapeCells + source.steps)
    (by simp [machine, Rewind.machine, recording, config]) (bridge_step p target source.final source.steps hh) reset'
  have joined := (by simpa only [Nat.zero_add, Nat.add_zero] using recorded :
    Prefix (machine p target) (source.peakTapeCells + source.steps) source.steps (recording c 0) (recording source.final source.steps)).trans bridge
  obtain ⟨r, hrun, hf, hs, hb⟩ := joined.run
    (by simp [machine, Rewind.machine, finished, config]) (by
      simp only [finished, Rewind.config_cells, List.length_replicate, Nat.add_zero]
      change source.final.tapeCells + source.steps ≤ _
      omega)
  exact ⟨r, by simpa only [Nat.add_zero, Nat.add_assoc, two_mul] using hrun,
    by simpa only [Nat.add_zero] using hf, by omega, hb⟩

end NearCubicWires.RepairOrdinary.SelectiveReset
