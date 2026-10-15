import Proof.Foundations.OrdinaryStreaming

/-! Paid head reset for an ordinary finite machine. One fresh unary tape logs
each original transition. On termination the controller consumes those marks,
moving every original head left once per mark, then halts. The original tapes
are unchanged during reset; erased counter cells remain charged as storage. -/
namespace NearCubicWires.RepairOrdinary.Rewind
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {t s : ℕ} (state : Fin (s + 2)) (heads : Fin t → ℕ)
    (tapes : Fin t → List Bool) (counterHead : ℕ) (counter : List Bool) :
    Configuration (t + 1) (s + 2) where
  control := state
  heads := Fin.addCases heads (fun _ => counterHead)
  tapes := Fin.addCases tapes (fun _ => counter)

def tapeCells {t : ℕ} (tapes : Fin t → List Bool) : ℕ := ∑ i, (tapes i).length

@[simp] theorem config_cells {t s : ℕ} (state : Fin (s + 2)) (heads : Fin t → ℕ)
    (tapes : Fin t → List Bool) (counterHead : ℕ) (counter : List Bool) :
    (config state heads tapes counterHead counter).tapeCells = tapeCells tapes + counter.length := by
  simp [Configuration.tapeCells, config, tapeCells, Fin.sum_univ_add]

def recording {t s : ℕ} (c : Configuration t s) (n : ℕ) : Configuration (t + 1) (s + 2) :=
  config (c.control.castAdd 2) c.heads c.tapes n (List.replicate n true)

def rewinding {t s : ℕ} (heads : Fin t → ℕ) (tapes : Fin t → List Bool) (n z : ℕ) :
    Configuration (t + 1) (s + 2) :=
  config ((0 : Fin 2).natAdd s) heads tapes (n - 1)
    (List.replicate n true ++ List.replicate z false)

def finished {t s : ℕ} (tapes : Fin t → List Bool) (n : ℕ) : Configuration (t + 1) (s + 2) :=
  config ((1 : Fin 2).natAdd s) (fun _ => 0) tapes 0 (List.replicate n false)

def recordAction {t s : ℕ} (a : Action t s) : Action (t + 1) (s + 2) where
  nextControl := a.nextControl.castAdd 2
  write := Fin.addCases a.write (fun _ => some true)
  move := Fin.addCases a.move (fun _ => .right)

def bridgeAction (t s : ℕ) : Action (t + 1) (s + 2) where
  nextControl := (0 : Fin 2).natAdd s
  write := fun _ => none
  move := Fin.addCases (fun _ => .stay) (fun _ => .left)

def rewindAction (t s : ℕ) : Action (t + 1) (s + 2) where
  nextControl := (0 : Fin 2).natAdd s
  write := Fin.addCases (fun _ => none) (fun _ => some false)
  move := fun _ => .left

def finishAction (t s : ℕ) : Action (t + 1) (s + 2) where
  nextControl := (1 : Fin 2).natAdd s
  write := fun _ => none
  move := fun _ => .stay

def machine {t s : ℕ} (p : Machine t s) : Machine (t + 1) (s + 2) where
  descriptionBits := 0
  start := p.start.castAdd 2
  halted := Fin.addCases (fun _ => false) (fun k => k.val == 1)
  rule := fun state scanned => Fin.addCases
    (fun c => if p.halted c then some (bridgeAction t s)
      else (p.rule c (fun i => scanned (i.castAdd 1))).map recordAction)
    (fun k => if k.val = 0 then
      if scanned ((0 : Fin 1).natAdd t) then some (rewindAction t s)
      else some (finishAction t s) else none) state

theorem rewind_step {t s : ℕ} (p : Machine t s) (heads : Fin t → ℕ)
    (tapes : Fin t → List Bool) (n z : ℕ) :
    step (machine p) (rewinding (s := s) heads tapes (n + 1) z) =
      some (rewinding (s := s) (fun i => heads i - 1) tapes n (z + 1)) := by
  have hr := Streaming.read_counter n z
  simp [step, machine, rewinding, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [applyAction, rewindAction, HeadMove.apply]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [applyAction, rewindAction, Streaming.erase_counter]

theorem finish_step {t s : ℕ} (p : Machine t s)
    (tapes : Fin t → List Bool) (z : ℕ) :
    step (machine p) (rewinding (s := s) (fun _ => 0) tapes 0 z) =
      some (finished (s := s) tapes z) := by
  simp [step, machine, rewinding, config, Configuration.scanned, Streaming.read_zeros]
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [applyAction, finishAction, finished, config, HeadMove.apply]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [applyAction, finishAction, finished, config]

theorem rewind_run {t s : ℕ} (p : Machine t s) (heads : Fin t → ℕ)
    (tapes : Fin t → List Bool) (n z : ℕ) (hh : ∀ i, heads i ≤ n) :
    ∃ r : ExecutionReceipt (t + 1) (s + 2),
      runFrom (machine p) (n + 1) (rewinding (s := s) heads tapes n z) = some r ∧
      r.final = finished (s := s) tapes (n + z) ∧ r.steps = n + 1 ∧
      r.peakTapeCells ≤ tapeCells tapes + n + z := by
  induction n generalizing heads z with
  | zero =>
    have hz : heads = fun _ => 0 := by funext i; have h := hh i; omega
    subst heads
    let suffix : ExecutionReceipt (t + 1) (s + 2) :=
      ⟨finished (s := s) tapes z, 0, (finished (s := s) tapes z).tapeCells⟩
    have hsuffix : runFrom (machine p) 0 (finished (s := s) tapes z) = some suffix := by
      simp [runFrom, machine, finished, config, suffix]
    have hj := runFrom_step (machine p) _ _ suffix
      (by simp [machine, rewinding, config]) (finish_step p tapes z) hsuffix
    refine ⟨_, hj, ?_, rfl, ?_⟩
    · simp [suffix]
    · simp [suffix, rewinding, finished]
  | succ n ih =>
    have hn : ∀ i, heads i - 1 ≤ n := by intro i; have h := hh i; omega
    obtain ⟨suffix, hsuffix, hf, hs, hp⟩ := ih (fun i => heads i - 1) (z + 1) hn
    have hj := runFrom_step (machine p) _ _ suffix
      (by simp [machine, rewinding, config]) (rewind_step p heads tapes n z) hsuffix
    refine ⟨⟨suffix.final, suffix.steps + 1,
      max (rewinding (s := s) heads tapes (n + 1) z).tapeCells suffix.peakTapeCells⟩,
      hj, ?_, ?_, ?_⟩
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf
    · dsimp only
      omega
    · simp only [rewinding, config_cells, List.length_append, List.length_replicate] at hp ⊢
      omega

theorem apply_record {t s : ℕ} (c : Configuration t s) (a : Action t s) (n : ℕ) :
    applyAction (recording c n) (recordAction a) = recording (applyAction c a) (n + 1) := by
  have hw : writeTapeBit (List.replicate n true) n true = List.replicate (n + 1) true := by
    simpa [List.replicate_add] using Streaming.write_append (List.replicate n true) true
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [applyAction, recordAction, recording, config, HeadMove.apply]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [applyAction, recordAction, recording, config, hw]

theorem record_step {t s : ℕ} (p : Machine t s) (c d : Configuration t s) (n : ℕ)
    (hn : p.halted c.control = false) (hs : step p c = some d) :
    step (machine p) (recording c n) = some (recording d (n + 1)) := by
  cases hr : p.rule c.control c.scanned with
  | none => simp [step, hr] at hs
  | some a =>
    have hd : applyAction c a = d := by simpa [step, hr] using hs
    subst d
    have hrule : (machine p).rule (recording c n).control (recording c n).scanned =
        some (recordAction a) := by
      simp [machine, recording, config, Configuration.scanned, hn]
      exact ⟨a, hr, rfl⟩
    simp only [step, hrule, Option.map_some, Option.some.injEq]
    exact apply_record c a n

theorem head_bound {t s : ℕ} (p : Machine t s) (c d : Configuration t s) (n : ℕ)
    (hh : ∀ i, c.heads i ≤ n) (hs : step p c = some d) : ∀ i, d.heads i ≤ n + 1 := by
  cases hr : p.rule c.control c.scanned with
  | none => simp [step, hr] at hs
  | some a =>
    have hd : applyAction c a = d := by simpa [step, hr] using hs
    subst d
    intro i
    have hi := hh i
    change (a.move i).apply (c.heads i) ≤ n + 1
    cases a.move i <;> simp only [HeadMove.apply] <;> omega

theorem bridge_step {t s : ℕ} (p : Machine t s) (c : Configuration t s) (n : ℕ)
    (hh : p.halted c.control = true) :
    step (machine p) (recording c n) = some (rewinding (s := s) c.heads c.tapes n 0) := by
  simp [step, machine, recording, config, hh]
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [applyAction, bridgeAction, rewinding, config, HeadMove.apply]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [applyAction, bridgeAction, rewinding, config]

theorem halted_run {t s : ℕ} (p : Machine t s) (c : Configuration t s) (n : ℕ)
    (hh : ∀ i, c.heads i ≤ n) (hc : p.halted c.control = true) :
    ∃ r : ExecutionReceipt (t + 1) (s + 2),
      runFrom (machine p) (n + 2) (recording c n) = some r ∧
      r.final = finished (s := s) c.tapes n ∧ r.steps = n + 2 ∧
      r.peakTapeCells ≤ c.tapeCells + n := by
  obtain ⟨suffix, hsuffix, hf, hs, hp⟩ := rewind_run p c.heads c.tapes n 0 hh
  have hj := runFrom_step (machine p) _ _ suffix
    (by simp [machine, recording, config]) (bridge_step p c n hc) hsuffix
  refine ⟨⟨suffix.final, suffix.steps + 1, max (recording c n).tapeCells suffix.peakTapeCells⟩,
    hj, ?_, ?_, ?_⟩
  · simpa using hf
  · dsimp only
    omega
  · simp only [recording, config_cells, List.length_replicate] at hp ⊢
    change max (c.tapeCells + n) suffix.peakTapeCells ≤ c.tapeCells + n
    exact max_le (Nat.le_refl _) (by simpa [tapeCells, Configuration.tapeCells] using hp)

theorem recorded_run {t s : ℕ} (p : Machine t s) (fuel : ℕ)
    (c : Configuration t s) (source : ExecutionReceipt t s)
    (hr : runFrom p fuel c = some source) (n : ℕ) (hh : ∀ i, c.heads i ≤ n) :
    ∃ r : ExecutionReceipt (t + 1) (s + 2),
      runFrom (machine p) (n + 2 * source.steps + 2) (recording c n) = some r ∧
      r.final = finished (s := s) source.final.tapes (n + source.steps) ∧
      r.steps = n + 2 * source.steps + 2 ∧
      r.peakTapeCells ≤ source.peakTapeCells + n + source.steps := by
  induction fuel generalizing c source n with
  | zero =>
    simp only [runFrom] at hr
    split at hr
    · next hc =>
      cases hr
      simpa using halted_run p c n hh hc
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hr
    split at hr
    · next hc =>
      cases hr
      simpa using halted_run p c n hh hc
    · next hc =>
      have hc' : p.halted c.control = false := by simpa using hc
      cases hs : step p c with
      | none => simp [hs] at hr
      | some d =>
        cases ht : runFrom p fuel d with
        | none => simp [hs, ht] at hr
        | some tail =>
          simp only [hs, ht, Option.some.injEq] at hr
          subst source
          obtain ⟨suffix, hsuffix, hf, hsteps, hpeak⟩ := ih d tail ht (n + 1) (head_bound p c d n hh hs)
          have hj := runFrom_step (machine p) _ _ suffix
            (by simp [machine, recording, config]) (record_step p c d n hc' hs) hsuffix
          refine ⟨⟨suffix.final, suffix.steps + 1,
            max (recording c n).tapeCells suffix.peakTapeCells⟩, ?_, ?_, ?_, ?_⟩
          · have hn : n + 2 * (tail.steps + 1) + 2 = n + 1 + 2 * tail.steps + 2 + 1 := by omega
            dsimp only
            rw [hn]
            exact hj
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf
          · dsimp only
            omega
          · simp only [recording, config_cells, List.length_replicate]
            change max (c.tapeCells + n) suffix.peakTapeCells ≤
              max c.tapeCells tail.peakTapeCells + n + (tail.steps + 1)
            have hcmax := Nat.le_max_left c.tapeCells tail.peakTapeCells
            have htmax := Nat.le_max_right c.tapeCells tail.peakTapeCells
            omega

theorem reset_run {t s : ℕ} (p : Machine t s) (fuel : ℕ) (input : Fin t → List Bool)
    (source : ExecutionReceipt t s) (hr : run p fuel input = some source) :
    ∃ r : ExecutionReceipt (t + 1) (s + 2),
      run (machine p) (2 * source.steps + 2) (Fin.addCases input (fun _ => [])) = some r ∧
      (∀ i : Fin t, r.final.tapes (i.castAdd 1) = source.final.tapes i) ∧
      (∀ i, r.final.heads i = 0) ∧ r.steps = 2 * source.steps + 2 ∧
      r.peakTapeCells ≤ source.peakTapeCells + source.steps := by
  obtain ⟨r, hrun, hf, hs, hp⟩ := recorded_run p fuel (initialConfiguration p input) source hr 0 (by simp [initialConfiguration])
  have hinit : recording (initialConfiguration p input) 0 =
      initialConfiguration (machine p) (Fin.addCases input (fun _ => [])) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp [recording, config, initialConfiguration]
    · rfl
  refine ⟨r, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hinit] at hrun
    simpa only [run, Nat.zero_add] using hrun
  · intro i
    simp [hf, finished, config]
  · intro i
    rw [hf]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [finished, config]
  · simpa using hs
  · simpa using hp

end NearCubicWires.RepairOrdinary.Rewind
