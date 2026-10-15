import Proof.Foundations.OrdinaryRewind

/-! Reusing retained zero-filled cells. Padding a tape with false cells does
not change its observations, but its allocated length remains charged. The
same finite program runs with identical steps on the padded configuration. -/
namespace NearCubicWires.RepairOrdinary.ZeroPadding
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pad (capacity : ℕ) (tape : List Bool) : List Bool :=
  tape ++ List.replicate (capacity - tape.length) false

@[simp] theorem pad_zero (tape : List Bool) : pad 0 tape = tape := by simp [pad]

theorem pad_cons (capacity : ℕ) (bit : Bool) (tape : List Bool) :
    pad capacity (bit :: tape) = bit :: pad (capacity - 1) tape := by
  have hn : capacity - (tape.length + 1) = (capacity - 1) - tape.length := by omega
  simp only [pad, List.length_cons, List.cons_append, hn]

theorem pad_nil_succ (capacity : ℕ) : pad (capacity + 1) [] = false :: pad capacity [] := by
  simp [pad, List.replicate_succ]

@[simp] theorem pad_length (capacity : ℕ) (tape : List Bool) :
    (pad capacity tape).length = max capacity tape.length := by
  simp only [pad, List.length_append, List.length_replicate]
  omega

theorem read_pad (capacity : ℕ) (tape : List Bool) (position : ℕ) :
    readTapeBit (pad capacity tape) position = readTapeBit tape position := by
  induction position generalizing capacity tape with
  | zero =>
    cases tape with
    | nil => cases capacity <;> rfl
    | cons b tape => simp [pad_cons, readTapeBit, List.getD]
  | succ position ih =>
    cases tape with
    | nil =>
      cases capacity with
      | zero => rfl
      | succ capacity =>
        simpa [pad_nil_succ, readTapeBit, List.getD] using ih capacity []
    | cons b tape =>
      simpa [pad_cons, readTapeBit, List.getD] using ih (capacity - 1) tape

theorem write_pad (capacity : ℕ) (tape : List Bool) (position : ℕ) (bit : Bool) :
    writeTapeBit (pad capacity tape) position bit = pad capacity (writeTapeBit tape position bit) := by
  induction position generalizing capacity tape with
  | zero =>
    cases tape with
    | nil =>
      cases capacity with
      | zero => simp
      | succ capacity => simp [pad_nil_succ, writeTapeBit, pad_cons]
    | cons b tape => simp [pad_cons, writeTapeBit]
  | succ position ih =>
    cases tape with
    | nil =>
      cases capacity with
      | zero => simp
      | succ capacity =>
        simpa [pad_nil_succ, writeTapeBit, pad_cons] using congrArg (List.cons false) (ih capacity [])
    | cons b tape =>
      simpa [pad_cons, writeTapeBit] using congrArg (List.cons b) (ih (capacity - 1) tape)

def config {t s : ℕ} (capacity : Fin t → ℕ) (c : Configuration t s) : Configuration t s where
  control := c.control
  heads := c.heads
  tapes := fun i => pad (capacity i) (c.tapes i)

def cells {t : ℕ} (capacity : Fin t → ℕ) : ℕ := ∑ i, capacity i

theorem config_cells {t s : ℕ} (capacity : Fin t → ℕ) (c : Configuration t s) :
    (config capacity c).tapeCells ≤ c.tapeCells + cells capacity := by
  simp only [Configuration.tapeCells, config, cells, pad_length, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  omega

theorem scanned_config {t s : ℕ} (capacity : Fin t → ℕ) (c : Configuration t s) :
    (config capacity c).scanned = c.scanned := by
  funext i
  exact read_pad (capacity i) (c.tapes i) (c.heads i)

theorem apply_config {t s : ℕ} (capacity : Fin t → ℕ) (c : Configuration t s) (a : Action t s) :
    applyAction (config capacity c) a = config capacity (applyAction c a) := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    cases hw : a.write i <;> simp [applyAction, config, hw, write_pad]

theorem step_config {t s : ℕ} (p : Machine t s) (capacity : Fin t → ℕ)
    (c d : Configuration t s) (hs : step p c = some d) :
    step p (config capacity c) = some (config capacity d) := by
  cases hr : p.rule c.control c.scanned with
  | none => simp [step, hr] at hs
  | some a =>
    have hd : applyAction c a = d := by simpa [step, hr] using hs
    subst d
    have hcontrol : (config capacity c).control = c.control := rfl
    simp only [step, hcontrol, scanned_config, hr, Option.map_some, Option.some.injEq]
    exact apply_config capacity c a

theorem run_config {t s : ℕ} (p : Machine t s) (capacity : Fin t → ℕ)
    (fuel : ℕ) (c : Configuration t s) (source : ExecutionReceipt t s)
    (hr : runFrom p fuel c = some source) :
    ∃ r : ExecutionReceipt t s, runFrom p fuel (config capacity c) = some r ∧
      r.final = config capacity source.final ∧ r.steps = source.steps ∧
      r.peakTapeCells ≤ source.peakTapeCells + cells capacity := by
  induction fuel generalizing c source with
  | zero =>
    simp only [runFrom] at hr
    split at hr
    · next hc =>
      cases hr
      refine ⟨⟨config capacity c, 0, (config capacity c).tapeCells⟩, ?_, rfl, rfl, config_cells capacity c⟩
      simp [runFrom, config, hc]
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hr
    split at hr
    · next hc =>
      cases hr
      refine ⟨⟨config capacity c, 0, (config capacity c).tapeCells⟩, ?_, rfl, rfl, config_cells capacity c⟩
      simp [runFrom, config, hc]
    · next hc =>
      cases hs : step p c with
      | none => simp [hs] at hr
      | some d =>
        cases ht : runFrom p fuel d with
        | none => simp [hs, ht] at hr
        | some tail =>
          simp only [hs, ht, Option.some.injEq] at hr
          subst source
          obtain ⟨suffix, hsuffix, hf, hsteps, hpeak⟩ := ih d tail ht
          have hnot : p.halted (config capacity c).control = false := by simpa [config] using hc
          have hj := runFrom_step p (config capacity c) (config capacity d) suffix hnot
            (step_config p capacity c d hs) hsuffix
          refine ⟨⟨suffix.final, suffix.steps + 1, max (config capacity c).tapeCells suffix.peakTapeCells⟩,
            hj, hf, ?_, ?_⟩
          · dsimp only
            omega
          · dsimp only
            have hb := config_cells capacity c
            have hcmax := Nat.le_max_left c.tapeCells tail.peakTapeCells
            have htmax := Nat.le_max_right c.tapeCells tail.peakTapeCells
            omega

end NearCubicWires.RepairOrdinary.ZeroPadding
