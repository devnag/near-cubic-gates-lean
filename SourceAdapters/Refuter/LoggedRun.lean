import SourceAdapters.Refuter.Body

/-!
# A step-logged run of the time constructor (input 7, the clock, part 1)

proof of `lem:multitape-refuter`, Step 1: "First `𝒟` computes `T(N)` and prepares its clock in `O(T(N)+1)` steps." The time
constructor (`TimeConstructible`, `L/Statement.lean:1033`) writes the binary digits of `T(N)` on its output tape
but says nothing about where its heads end or how long the output list is. `logged p` runs `p` unchanged on its
own tapes and, on one extra tape, writes one `1` per step: when `p` halts after `s` steps the extra tape is
`1^s` with its head at `s` (`logged_run`). Every head of `p` and the output's length are then at most `s`
(`run_bounds`), which is what the binary-to-unary conversion needs.
-/

namespace NearCubicGates.Adapters.Refuter.Clock

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

variable {t s : ℕ}

def logAction (a : Action t s) : Action (t + 1) s where
  nextControl := a.nextControl
  write := Fin.addCases a.write (fun _ => some true)
  move := Fin.addCases a.move (fun _ => .right)

/-- `p` with a step log on one extra tape. -/
def logged (p : Machine t s) : Machine (t + 1) s where
  descriptionBits := 0
  start := p.start
  halted := p.halted
  rule := fun q scanned => (p.rule q (fun i => scanned (i.castAdd 1))).map logAction

def logConfig (c : Configuration t s) (n : ℕ) : Configuration (t + 1) s where
  control := c.control
  heads := Fin.addCases c.heads (fun _ => n)
  tapes := Fin.addCases c.tapes (fun _ => List.replicate n true)

theorem wtb_rep (n : ℕ) : writeTapeBit (List.replicate n true) n true = List.replicate (n + 1) true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, writeTapeBit, ih]

theorem log_step (p : Machine t s) (c d : Configuration t s) (n : ℕ) (hs : step p c = some d) :
    step (logged p) (logConfig c n) = some (logConfig d (n + 1)) := by
  cases hr : p.rule c.control c.scanned with
  | none => simp [step, hr] at hs
  | some a =>
    have hd : applyAction c a = d := by simpa [step, hr] using hs
    subst d
    have hsc : (fun i : Fin t => (logConfig c n).scanned (i.castAdd 1)) = c.scanned := by
      funext i; simp [Configuration.scanned, logConfig]
    have hctl : (logConfig c n).control = c.control := rfl
    show Option.map (applyAction (logConfig c n))
      ((p.rule (logConfig c n).control (fun i => (logConfig c n).scanned (i.castAdd 1))).map logAction) = _
    rw [hctl, hsc, hr]
    simp only [Option.map_some, Option.some.injEq]
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [applyAction, logAction, logConfig, HeadMove.apply]
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [applyAction, logAction, logConfig, wtb_rep]

/-- **The logged run**: the log tape holds `1^s` with its head at `s` after `s` steps. -/
theorem logged_run (p : Machine t s) : ∀ (fuel : ℕ) (c : Configuration t s) (r : ExecutionReceipt t s) (n : ℕ),
    runFrom p fuel c = some r →
      ∃ r', runFrom (logged p) fuel (logConfig c n) = some r' ∧ r'.final = logConfig r.final (n + r.steps) ∧
        r'.steps = r.steps := by
  intro fuel
  induction fuel with
  | zero =>
    intro c r n hr
    simp only [runFrom] at hr
    split at hr
    · next hh =>
      cases hr
      refine ⟨⟨logConfig c n, 0, (logConfig c n).tapeCells⟩, ?_, by simp, rfl⟩
      simp only [runFrom]; rw [if_pos (by simpa [logged, logConfig] using hh)]
    · contradiction
  | succ fuel ih =>
    intro c r n hr
    simp only [runFrom] at hr
    split at hr
    · next hh =>
      cases hr
      refine ⟨⟨logConfig c n, 0, (logConfig c n).tapeCells⟩, ?_, by simp, rfl⟩
      simp only [runFrom]; rw [if_pos (by simpa [logged, logConfig] using hh)]
    · next hh =>
      cases hs : step p c with
      | none => simp [hs] at hr
      | some d =>
        cases ht : runFrom p fuel d with
        | none => simp [hs, ht] at hr
        | some tail =>
          simp only [hs, ht, Option.some.injEq] at hr
          subst hr
          obtain ⟨r', h1, h2, h3⟩ := ih d tail (n + 1) ht
          refine ⟨_, runFrom_step (logged p) _ _ _ (by simpa [logged, logConfig] using hh) (log_step p c d n hs) h1,
            ?_, ?_⟩
          · simp only [h2]; congr 1; omega
          · simp [h3]

/-- Heads and fresh tapes stay within the step count. -/
theorem run_bounds (p : Machine t s) : ∀ (fuel : ℕ) (c : Configuration t s) (r : ExecutionReceipt t s) (A : ℕ),
    runFrom p fuel c = some r → (∀ i, c.heads i ≤ A) →
      (∀ i, r.final.heads i ≤ A + r.steps) ∧ ∀ i, (c.tapes i).length ≤ A → (r.final.tapes i).length ≤ A + r.steps := by
  intro fuel
  induction fuel with
  | zero =>
    intro c r A hr hh
    simp only [runFrom] at hr
    split at hr
    · cases hr; exact ⟨fun i => by simpa using hh i, fun i h => by simpa using h⟩
    · contradiction
  | succ fuel ih =>
    intro c r A hr hh
    simp only [runFrom] at hr
    split at hr
    · cases hr; exact ⟨fun i => by simpa using hh i, fun i h => by simpa using h⟩
    · cases hs : step p c with
      | none => simp [hs] at hr
      | some d =>
        cases ht : runFrom p fuel d with
        | none => simp [hs, ht] at hr
        | some tail =>
          simp only [hs, ht, Option.some.injEq] at hr
          subst hr
          cases ha : p.rule c.control c.scanned with
          | none => simp [step, ha] at hs
          | some a =>
            have hd : applyAction c a = d := by simpa [step, ha] using hs
            subst d
            have hh' : ∀ i, (applyAction c a).heads i ≤ A + 1 := by
              intro i
              have := hh i
              change (a.move i).apply (c.heads i) ≤ A + 1
              cases a.move i <;> simp [HeadMove.apply] <;> omega
            obtain ⟨b1, b2⟩ := ih (applyAction c a) tail (A + 1) ht hh'
            refine ⟨fun i => by have := b1 i; simp only; omega, fun i hl => ?_⟩
            have : ((applyAction c a).tapes i).length ≤ A + 1 := by
              simp only [applyAction]
              cases a.write i with
              | none => simp only; omega
              | some v =>
                simp only [NearCubicGates.Adapters.Refuter.Mach.wtb_length]
                have := hh i; omega
            have := b2 i this; simp only; omega

end NearCubicGates.Adapters.Refuter.Clock
