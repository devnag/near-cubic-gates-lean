import SourceAdapters.Refuter.FaithfulPrefix

/-!
# Tape-by-tape checking of a guessed computation (input 7, F01 semantic bridge)

Paper anchor: `lem:multitape-refuter`, "The universal simulation": "Composing the
tape reduction with that simulator gives a fixed universal nondeterministic acceptor `U` that
preserves the language of each simulated machine `P`: if `P` has an accepting computation of
length `t` on `u`, then `U` on its code and `u` has one of length at most `c_P(t+1)`."

The tape reduction is SFM78 Lemma 3 (BGW70). Its construction, `adapters/sourcetext/SFM78.txt`
l.222–233: "The first task for M' is to nondeterministically guess on its second tape an alternating
sequence of displays and legal actions by M. The question of whether the sequence describes a legal
computation by M on the supplied input is just the question of whether the symbols actually scanned
on each tape when the actions are taken agree with the guessed displays. This can be checked
independently for each tape in turn by letting the first tape of M' play the role of the tape while
running through the guessed sequence of displays and actions. Clearly M' runs for time proportional
to the length of the sequence it guesses."

This module proves that construction's correctness for the local bit model, combined with the
protected cutoff of `FaithfulPrefix`: a guessed sequence passes the per-tape checks
**iff** it is the cut run on the copied prefixes. The guessed sequence has one entry per simulated
step, so a computation of `t` steps is certified by a guess of `t` entries; each tape is replayed
once. The fixed machine that performs these checks with cost `a_M + b_M(t+1)` is the machine-level construction (it is where the constant `c_P` of proof of `lem:multitape-refuter` is paid).

-/

namespace NearCubicGates.Adapters.Refuter

open NearCubicWires NearCubicWires.LocalBitMultitape

set_option autoImplicit false

/-- One guessed step: the scanned bits of all tapes (the display without the control state, which
is recomputed) and the action taken (SFM78 l.222–224, "displays and legal actions"). -/
structure ClaimedStep (t s : ℕ) where
  scanned : Fin t → Bool
  action : Action t s

/-- The control state after a guessed sequence, recomputed from the actions. -/
def controlAfter {t s : ℕ} (q : Fin s) : List (ClaimedStep t s) → Fin s
  | [] => q
  | e :: rest => controlAfter e.action.nextControl rest

/-- Every guessed action is the legal transition of `m` at the current control and the guessed
display, taken from a non-halted control. -/
def ControlLegal {t s : ℕ} (m : Machine t s) : Fin s → List (ClaimedStep t s) → Prop
  | _, [] => True
  | q, e :: rest => m.halted q = false ∧ m.rule q e.scanned = some e.action ∧
      ControlLegal m e.action.nextControl rest

/-- The tape after one guessed action on tape `i`. -/
def replayWrite {t s : ℕ} (i : Fin t) (e : ClaimedStep t s) (tape : List Bool) (head : ℕ) :
    List Bool :=
  match e.action.write i with
  | none => tape
  | some b => writeTapeBit tape head b

/-- Replay of tape `i` alone through the guessed sequence (SFM78 l.227–230): before each step the
head is strictly before the protected cutoff `r` and scans the guessed bit; the guessed write and
move are then applied. -/
def TapeReplay {t s : ℕ} (r : ℕ) (i : Fin t) : List Bool → ℕ → List (ClaimedStep t s) → Prop
  | _, _, [] => True
  | tape, head, e :: rest => head < r ∧ readTapeBit tape head = e.scanned i ∧
      TapeReplay r i (replayWrite i e tape head) ((e.action.move i).apply head) rest

/-- All checks from a configuration: legal controls, every tape replays, the final control is
halted. -/
def ChecksFrom {t s : ℕ} (m : Machine t s) (r : ℕ) (c : Configuration t s)
    (trace : List (ClaimedStep t s)) : Prop :=
  ControlLegal m c.control trace ∧ (∀ i, TapeReplay r i (c.tapes i) (c.heads i) trace) ∧
    m.halted (controlAfter c.control trace) = true

/-- All checks on the copied prefixes of the initial tapes (heads at zero, control `start`). -/
def TraceChecks {t s : ℕ} (m : Machine t s) (r : ℕ) (tapes : Fin t → List Bool)
    (trace : List (ClaimedStep t s)) : Prop :=
  ChecksFrom m r (initialConfiguration m (prefixTapes r tapes)) trace

/-! ## Per-tape checks are equivalent to the joint cut run -/

theorem applyAction_tapes' {t s : ℕ} (c : Configuration t s) (a : Action t s)
    (sc : Fin t → Bool) (i : Fin t) :
    (applyAction c a).tapes i = replayWrite i ⟨sc, a⟩ (c.tapes i) (c.heads i) := by
  cases h : a.write i <;> simp [applyAction, replayWrite, h]

theorem applyAction_tapes {t s : ℕ} (c : Configuration t s) (e : ClaimedStep t s) (i : Fin t) :
    (applyAction c e.action).tapes i = replayWrite i e (c.tapes i) (c.heads i) :=
  applyAction_tapes' c e.action e.scanned i

/-- **Soundness, for every guessed sequence**: passing the checks makes the cut run halt, with any
fuel at least the guess length, at the recomputed control. -/
theorem checks_sound {t s : ℕ} (m : Machine t s) (r : ℕ) :
    ∀ (trace : List (ClaimedStep t s)) (c : Configuration t s) (fuel : ℕ),
      trace.length ≤ fuel → ChecksFrom m r c trace →
      ∃ d, cutRunFrom m r fuel c = some d ∧ d.control = controlAfter c.control trace := by
  intro trace
  induction trace with
  | nil =>
    intro c fuel _ h
    have hh : m.halted c.control = true := h.2.2
    refine ⟨c, ?_, rfl⟩
    cases fuel <;> simp [cutRunFrom, hh]
  | cons e rest ih =>
    intro c fuel hfuel h
    obtain ⟨hctl, htapes, hfinal⟩ := h
    obtain ⟨hnh, hrule, hrest⟩ := hctl
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hlt : ∀ i, c.heads i < r := fun i => (htapes i).1
    have hscan : c.scanned = e.scanned := by
      funext i
      exact (htapes i).2.1
    have hstep : step m c = some (applyAction c e.action) := by
      simp [step, hscan, hrule]
    have hcut : ¬ ∃ i, r ≤ c.heads i := by
      rintro ⟨i, hi⟩
      exact absurd (hlt i) (Nat.not_lt.mpr hi)
    have hnext : ChecksFrom m r (applyAction c e.action) rest := by
      refine ⟨hrest, fun i => ?_, hfinal⟩
      rw [applyAction_tapes]
      exact (htapes i).2.2
    obtain ⟨d, hd, hdc⟩ := ih (applyAction c e.action) f (by simp at hfuel; omega) hnext
    refine ⟨d, ?_, hdc⟩
    simp [cutRunFrom, hnh, hcut, hstep, hd]

/-- **Completeness**: a halted cut run is described by a guessed sequence of length at most its
fuel that passes all checks. -/
theorem checks_complete {t s : ℕ} (m : Machine t s) (r : ℕ) :
    ∀ (fuel : ℕ) (c d : Configuration t s), cutRunFrom m r fuel c = some d →
      ∃ trace : List (ClaimedStep t s), trace.length ≤ fuel ∧ ChecksFrom m r c trace ∧
        controlAfter c.control trace = d.control := by
  intro fuel
  induction fuel with
  | zero =>
    intro c d h
    simp only [cutRunFrom] at h
    split_ifs at h with hh
    cases h
    exact ⟨[], le_rfl, ⟨trivial, fun _ => trivial, hh⟩, rfl⟩
  | succ f ih =>
    intro c d h
    simp only [cutRunFrom] at h
    split_ifs at h with hh hcut
    · cases h
      exact ⟨[], Nat.zero_le _, ⟨trivial, fun _ => trivial, hh⟩, rfl⟩
    · cases hrule : m.rule c.control c.scanned with
      | none => simp [step, hrule] at h
      | some a =>
        have hstep : step m c = some (applyAction c a) := by simp [step, hrule]
        rw [hstep] at h
        obtain ⟨rest, hlen, hchk, hctl⟩ := ih _ d h
        refine ⟨⟨c.scanned, a⟩ :: rest, by simp; omega, ⟨⟨by simpa using hh, hrule, hchk.1⟩,
          fun i => ⟨?_, rfl, ?_⟩, hchk.2.2⟩, hctl⟩
        · exact Nat.lt_of_not_le fun hle => hcut ⟨i, hle⟩
        · have := hchk.2.1 i
          rw [applyAction_tapes' c a c.scanned i] at this
          exact this

/-! ## The accepted-time bridge at the verifier level -/

/-- A run that halts is reproduced with fuel exactly its step count. -/
theorem runFrom_exact {t s : ℕ} (m : Machine t s) :
    ∀ (fuel : ℕ) (c : Configuration t s) (receipt : ExecutionReceipt t s),
      runFrom m fuel c = some receipt → runFrom m receipt.steps c = some receipt := by
  intro fuel
  induction fuel with
  | zero =>
    intro c receipt h
    simp only [runFrom] at h
    split_ifs at h with hh
    cases h
    simp [runFrom, hh]
  | succ f ih =>
    intro c receipt h
    simp only [runFrom] at h
    split_ifs at h with hh
    · cases h
      simp [runFrom, hh]
    · cases hs : step m c with
      | none => simp [hs] at h
      | some next =>
        cases hr : runFrom m f next with
        | none => simp [hs, hr] at h
        | some suffix =>
          simp only [hs, hr, Option.some.injEq] at h
          subst h
          have := ih next suffix hr
          simp [runFrom, hh, hs, this]

/-- **Every certified verdict is genuine** (for every cutoff `r` and every guessed sequence): if a
guessed sequence passes the checks on the copied framed tapes, the original framed run halts within
the guess length, in the recomputed control state. -/
theorem trace_genuine (v : RepairOrdinary.Verifier) (r : ℕ) (x w : List Bool)
    (trace : List (ClaimedStep v.tapeCount v.stateCount))
    (h : TraceChecks v.machine r (v.inputTapes x w) trace) :
    ∃ receipt, run v.machine trace.length (v.inputTapes x w) = some receipt ∧
      receipt.final.control = controlAfter v.machine.start trace := by
  obtain ⟨d, hd, hdc⟩ := checks_sound v.machine r trace _ trace.length le_rfl h
  obtain ⟨receipt, hrun, hf⟩ :=
    cutRun_sound v.machine r trace.length _ _ d (prefixFaithful_initial _ r _) hd
  exact ⟨receipt, hrun, by rw [← hf.control, hdc]; rfl⟩

/-- **The useful guess exists** (proof of `lem:multitape-refuter` with SFM78 l.231–232): if the original framed run
halts within `t` steps, a guessed sequence of at most `t` entries passes the checks at the cutoff
`t + 2` and recomputes the actual final control (hence the actual verdict). -/
theorem trace_useful (v : RepairOrdinary.Verifier) (t fuel : ℕ) (x w : List Bool)
    (receipt : ExecutionReceipt v.tapeCount v.stateCount)
    (hrun : run v.machine fuel (v.inputTapes x w) = some receipt) (ht : receipt.steps ≤ t) :
    ∃ trace : List (ClaimedStep v.tapeCount v.stateCount), trace.length ≤ t ∧
      TraceChecks v.machine (t + 2) (v.inputTapes x w) trace ∧
      controlAfter v.machine.start trace = receipt.final.control := by
  have hexact := runFrom_exact v.machine fuel _ receipt hrun
  obtain ⟨d, hd, hf⟩ := cutRun_complete v.machine (t + 2) receipt.steps _ _ receipt hexact
    (prefixFaithful_initial _ (t + 2) _) (fun i => by
      simp only [initialConfiguration]
      omega)
  obtain ⟨trace, hlen, hchk, hctl⟩ := checks_complete v.machine (t + 2) receipt.steps _ d hd
  exact ⟨trace, by omega, hchk, hctl.trans hf.control⟩

/-- The weak-machine instance (proof of `cor:framed-refuter`): every framed run of a promised weak machine on a
witness of exactly `⌊n/16⌋` bits is certified, with its actual verdict, by a guess of at most
`t_M(n)` entries at the cutoff `t_M(n) + 2`. -/
theorem weak_trace_useful (M : RepairSource.OrdinaryWeakMachine) (n : ℕ) (x : BitInput n)
    (w : BitInput (n / 16)) :
    ∃ trace : List (ClaimedStep M.verifier.tapeCount M.verifier.stateCount),
      trace.length ≤ M.runtime n ∧
      TraceChecks M.verifier.machine (M.runtime n + 2)
        (M.verifier.inputTapes (List.ofFn x) (List.ofFn w)) trace ∧
      (M.verifier.accepting (controlAfter M.verifier.machine.start trace) = true ↔
        M.verifier.acceptsAt (M.runtime n) (List.ofFn x) (List.ofFn w)) := by
  obtain ⟨receipt, hrun⟩ := M.halts n x w
  obtain ⟨trace, hlen, hchk, hctl⟩ :=
    trace_useful M.verifier (M.runtime n) (M.runtime n) _ _ receipt hrun
      (runFrom_steps_le _ _ _ _ hrun)
  refine ⟨trace, hlen, hchk, ?_⟩
  rw [hctl]
  constructor
  · exact fun h => ⟨receipt, hrun, h⟩
  · rintro ⟨r', hr', hacc⟩
    rw [hrun] at hr'
    cases hr'
    exact hacc

end NearCubicGates.Adapters.Refuter
