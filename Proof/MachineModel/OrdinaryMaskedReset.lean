import Proof.MachineModel.OrdinarySelectiveWorkspace

/-! Reset the bounded local heads needed by the memory-check loop in one
recorded pass. Global source/output cursors are excluded by the mask. This
is the existing selective-reset algorithm with several selected heads, not
a free configuration reset; the counter and every rewind step are executed.
-/
namespace NearCubicWires.RepairOrdinary.MaskedReset
open LocalBitMultitape
open Rewind (config recording rewinding tapeCells recordAction bridgeAction finishAction)
open SelectiveReset (finished)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rewindAction {t : ℕ} (s : ℕ) (selected : Fin t → Bool) : Action (t+1) (s+2) where
  nextControl := (0 : Fin 2).natAdd s
  write := Fin.addCases (fun _ => none) (fun _ => some false)
  move := Fin.addCases (fun i => if selected i then .left else .stay) (fun _ => .left)
def machine {t s : ℕ} (p : Machine t s) (selected : Fin t → Bool) : Machine (t+1) (s+2) where
  descriptionBits := 0
  start := p.start.castAdd 2
  halted := (Rewind.machine p).halted
  rule := fun state scanned => Fin.addCases
    (fun c => if p.halted c then some (bridgeAction t s)
      else (p.rule c (fun i => scanned (i.castAdd 1))).map recordAction)
    (fun k => if k.val = 0 then
      if scanned ((0 : Fin 1).natAdd t) then some (rewindAction s selected)
      else some (finishAction t s) else none) state

theorem record_step {t s : ℕ} (p : Machine t s) (selected : Fin t → Bool)
    (c d : Configuration t s) (n : ℕ) (hn : p.halted c.control = false)
    (hs : step p c = some d) :
    step (machine p selected) (recording c n) = some (recording d (n+1)) := by
  have h := Rewind.record_step p c d n hn hs
  simpa only [step, machine, Rewind.machine, recording, config, Fin.addCases_left] using h

theorem bridge_step {t s : ℕ} (p : Machine t s) (selected : Fin t → Bool)
    (c : Configuration t s) (n : ℕ) (hh : p.halted c.control = true) :
    step (machine p selected) (recording c n) = some (rewinding (s := s) c.heads c.tapes n 0) := by
  have h := Rewind.bridge_step p c n hh
  simpa only [step, machine, Rewind.machine, recording, config, Fin.addCases_left] using h

theorem rewind_step {t s : ℕ} (p : Machine t s) (selected : Fin t → Bool)
    (heads : Fin t → ℕ) (tapes : Fin t → List Bool) (n z : ℕ) :
    step (machine p selected) (rewinding (s := s) heads tapes (n+1) z) =
      some (rewinding (s := s) (fun i => if selected i then heads i-1 else heads i) tapes n (z+1)) := by
  have hr := Streaming.read_counter n z
  simp [step, machine, rewinding, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · cases h : selected j <;> simp [applyAction, rewindAction, HeadMove.apply, h]
    · simp [applyAction, rewindAction, HeadMove.apply]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [applyAction, rewindAction, Streaming.erase_counter]

theorem finish_step {t s : ℕ} (p : Machine t s) (selected : Fin t → Bool)
    (heads : Fin t → ℕ) (tapes : Fin t → List Bool) (z : ℕ) :
    step (machine p selected) (rewinding (s := s) heads tapes 0 z) =
      some (finished (s := s) heads tapes z) := by
  simp [step, machine, rewinding, config, Configuration.scanned, Streaming.read_zeros]
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [applyAction, finishAction, finished, config, HeadMove.apply]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [applyAction, finishAction, finished, config]

theorem rewind_prefix {t s : ℕ} (p : Machine t s) (selected : Fin t → Bool)
    (heads : Fin t → ℕ) (tapes : Fin t → List Bool) (n z : ℕ) :
    Prefix (machine p selected) (tapeCells tapes+n+z) (n+1)
      (rewinding (s := s) heads tapes n z)
      (finished (s := s) (fun i => if selected i then heads i-n else heads i) tapes (n+z)) := by
  induction n generalizing heads z with
  | zero =>
    simpa using Prefix.step
      (by simp [rewinding] : (rewinding (s := s) heads tapes 0 z).tapeCells ≤ tapeCells tapes+z)
      (by simp [machine, Rewind.machine, rewinding, config]) (finish_step p selected heads tapes z)
      (Prefix.refl _ (by simp [finished]))
  | succ n ih =>
    let next := fun i => if selected i then heads i-1 else heads i
    have ht := ih next (z+1)
    have hend : (fun i => if selected i then next i-n else next i) =
        fun i => if selected i then heads i-(n+1) else heads i := by
      funext i
      cases h : selected i <;> simp [next, h, Nat.sub_sub, Nat.add_comm 1 n]
    rw [hend] at ht
    have hj := Prefix.step
      (by simp [rewinding]; omega : (rewinding (s := s) heads tapes (n+1) z).tapeCells ≤ tapeCells tapes+n+(z+1))
      (by simp [machine, Rewind.machine, rewinding, config]) (rewind_step p selected heads tapes n z) ht
    simpa only [Nat.add_assoc, Nat.add_comm 1 z] using hj

theorem recording_prefix {t s space n : ℕ} {p : Machine t s} {c d : Configuration t s}
    (hp : Prefix p space n c d) (selected : Fin t → Bool) (count : ℕ) :
    Prefix (machine p selected) (space+count+n) n (recording c count) (recording d (count+n)) := by
  induction hp generalizing count with
  | refl c hc =>
    exact Prefix.refl _ (by
      simp only [recording, Rewind.config_cells, List.length_replicate, Nat.add_zero]
      change c.tapeCells+count ≤ space+count
      omega)
  | @step n c d e hc hn hs _ ih =>
    have ht := ih (count+1)
    have hj := Prefix.step
      (by
        simp only [recording, Rewind.config_cells, List.length_replicate]
        change c.tapeCells+count ≤ space+(count+1)+n
        omega : (recording c count).tapeCells ≤ space+(count+1)+n)
      (by simp [machine, Rewind.machine, recording, config]) (record_step p selected c d count hn hs) ht
    simpa only [Nat.add_assoc, Nat.add_comm 1 n] using hj

theorem reset_run {t s : ℕ} (p : Machine t s) (selected : Fin t → Bool) (fuel : ℕ)
    (c : Configuration t s) (source : ExecutionReceipt t s)
    (hr : runFrom p fuel c = some source)
    (hhead : ∀ i, selected i = true → source.final.heads i ≤ source.steps) :
    ∃ r : ExecutionReceipt (t+1) (s+2),
      runFrom (machine p selected) (2*source.steps+2) (recording c 0) = some r ∧
      r.final = finished (s := s) (fun i => if selected i then 0 else source.final.heads i)
        source.final.tapes source.steps ∧ r.steps = 2*source.steps+2 ∧
      r.peakTapeCells ≤ source.peakTapeCells+source.steps := by
  obtain ⟨hp, hh⟩ := prefix_of_run p fuel c source hr
  have hc := SortMatrix.final_cells hp
  have recorded := recording_prefix hp selected 0
  have reset := rewind_prefix p selected source.final.heads source.final.tapes source.steps 0
  have hheads : (fun i => if selected i then source.final.heads i-source.steps else source.final.heads i) =
      fun i => if selected i then 0 else source.final.heads i := by
    funext i
    cases hi : selected i
    · simp
    · simp [Nat.sub_eq_zero_of_le (hhead i hi)]
  rw [hheads] at reset
  have reset' := reset.enlarge (large := source.peakTapeCells+source.steps) (by
    change source.final.tapeCells+source.steps+0 ≤ _
    omega)
  have bridge := Prefix.step
    (by
      simp only [recording, Rewind.config_cells, List.length_replicate]
      change source.final.tapeCells+source.steps ≤ _
      omega : (recording source.final source.steps).tapeCells ≤ source.peakTapeCells+source.steps)
    (by simp [machine, Rewind.machine, recording, config]) (bridge_step p selected source.final source.steps hh) reset'
  have joined := (by simpa only [Nat.zero_add, Nat.add_zero] using recorded :
    Prefix (machine p selected) (source.peakTapeCells+source.steps) source.steps
      (recording c 0) (recording source.final source.steps)).trans bridge
  obtain ⟨r, hrun, hf, hs, hb⟩ := joined.run
    (by simp [machine, Rewind.machine, finished, config]) (by
      simp only [finished, Rewind.config_cells, List.length_replicate, Nat.add_zero]
      change source.final.tapeCells+source.steps ≤ _
      omega)
  exact ⟨r, by simpa only [Nat.add_zero, Nat.add_assoc, two_mul] using hrun,
    by simpa only [Nat.add_zero] using hf, by omega, hb⟩

theorem workspace_run {t s : ℕ} (p : Machine t s) (selected : Fin t → Bool) (fuel cap : ℕ)
    (c : Configuration t s) (source : ExecutionReceipt t s)
    (hr : runFrom p fuel c = some source)
    (hstart : ∀ i, selected i = true → c.heads i = 0) (hcap : source.steps ≤ cap) :
    ∃ r : ExecutionReceipt (t+1) (s+2),
      runFrom (machine p selected) (2*source.steps+2)
        (ZeroPadding.config (Rewind.Workspace.capacities t cap) (recording c 0)) = some r ∧
      r.final = finished (s := s) (fun i => if selected i then 0 else source.final.heads i)
        source.final.tapes cap ∧ r.steps = 2*source.steps+2 ∧
      r.peakTapeCells ≤ source.peakTapeCells+source.steps+cap := by
  have hhead : ∀ i, selected i = true → source.final.heads i ≤ source.steps := by
    intro i hi
    have h := SelectiveReset.prefix_head (prefix_of_run p fuel c source hr).1 i
    simpa only [hstart i hi, zero_add] using h
  obtain ⟨base, hb, hf, hs, hp⟩ := reset_run p selected fuel c source hr hhead
  obtain ⟨r, hrun, hfinal, hsteps, hpeak⟩ := ZeroPadding.run_config (machine p selected)
    (Rewind.Workspace.capacities t cap) _ _ base hb
  refine ⟨r, hrun, ?_, hsteps.trans hs, ?_⟩
  · rw [hfinal, hf, SelectiveReset.padded_finished, max_eq_left hcap]
  · rw [Rewind.Workspace.capacity_cells] at hpeak
    omega

end NearCubicWires.RepairOrdinary.MaskedReset
