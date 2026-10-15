import Proof.MachineModel.OrdinaryOracleComposeTrace

/-! A unary record of actual local transitions survives a paid final rewind.
Oracle asks retain their original cost and change neither tape nor head. -/
namespace NearCubicWires.RepairSource.OrdinaryOracleCompose
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clockAction {t s : ℕ} (a : Action t s) : Action (t + 1) s where
  nextControl := a.nextControl
  write := Fin.addCases a.write (fun _ => some true)
  move := Fin.addCases a.move (fun _ => .right)

def clockMachine {t s : ℕ} (p : Machine t s) : Machine (t + 1) s where
  descriptionBits := 0
  start := p.start
  halted := p.halted
  rule := fun q scanned =>
    (p.rule q (fun i => scanned (i.castAdd 1))).map clockAction

def clockConfig {t s : ℕ} (c : Configuration t s) (n : ℕ) :
    Configuration (t + 1) s where
  control := c.control
  heads := Fin.addCases c.heads (fun _ => n)
  tapes := Fin.addCases c.tapes (fun _ => List.replicate n true)

def clockRecord {t s : ℕ} (c : Configuration t s) (n : ℕ) :=
  Rewind.recording (clockConfig c n) n

def clockReturn {s : ℕ} (r : OracleReturn s) : OracleReturn (s + 2) :=
  ⟨r.onFalse.castAdd 2, r.onTrue.castAdd 2⟩

def clocked (p : OrdinaryOracleProgram) : OrdinaryOracleProgram where
  base := {
    tapeCount := (p.base.tapeCount + 1) + 1
    stateCount := p.base.stateCount + 2
    twoTapes := by omega
    machine := Rewind.machine (clockMachine p.base.machine)
    outputTape := (p.base.outputTape.castAdd 1).castAdd 1
    outputFresh := p.base.outputFresh }
  queryTape := (p.queryTape.castAdd 1).castAdd 1
  queryFresh := p.queryFresh
  query := Fin.addCases (fun q => if p.base.machine.halted q then none
    else (p.query q).map clockReturn) (fun _ => none)

theorem clock_apply {t s : ℕ} (c : Configuration t s) (a : Action t s) (n : ℕ) :
    applyAction (clockConfig c n) (clockAction a) = clockConfig (applyAction c a) (n + 1) := by
  have hw : writeTapeBit (List.replicate n true) n true = List.replicate (n + 1) true := by
    simp [List.replicate_add]
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [applyAction, clockAction, clockConfig, HeadMove.apply]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [applyAction, clockAction, clockConfig, hw]

theorem clock_step {t s : ℕ} (p : Machine t s) (c d : Configuration t s) (n : ℕ)
    (hs : step p c = some d) :
    step (clockMachine p) (clockConfig c n) = some (clockConfig d (n + 1)) := by
  cases hr : p.rule c.control c.scanned with
  | none => simp [step, hr] at hs
  | some a =>
    have hd : applyAction c a = d := by simpa [step, hr] using hs
    subst d
    have hscan : (fun i => (clockConfig c n).scanned (i.castAdd 1)) = c.scanned := by
      funext i
      simp [clockConfig, Configuration.scanned]
    have hrule : (clockMachine p).rule (clockConfig c n).control (clockConfig c n).scanned =
        some (clockAction a) := by
      change (p.rule c.control (fun i => (clockConfig c n).scanned (i.castAdd 1))).map
        clockAction = some (clockAction a)
      rw [hscan, hr]
      rfl
    simp only [step, hrule, Option.map_some, Option.some.injEq]
    exact clock_apply c a n

theorem clock_local {o : ℕ → Bool} {p : OrdinaryOracleProgram}
    {c d : p.Config} (n : ℕ) (hh : p.base.machine.halted c.control = false)
    (hq : p.query c.control = none) (hs : step p.base.machine c = some d) :
    OrdinaryOracleStep o (clocked p) 1 (clockRecord c n) (clockRecord d (n + 1)) := by
  refine .local _ _ ?_ ?_ ?_
  · simp [clocked, clockRecord, Rewind.machine, Rewind.recording, Rewind.config]
  · simp [clocked, clockRecord, Rewind.recording, Rewind.config, clockConfig, hh, hq]
  · exact Rewind.record_step (clockMachine p.base.machine) (clockConfig c n)
      (clockConfig d (n + 1)) n hh (clock_step p.base.machine c d n hs)

theorem clock_ask {o : ℕ → Bool} {p : OrdinaryOracleProgram}
    (c : p.Config) (n : ℕ) (bits padding : List Bool)
    (rule : OracleReturn p.base.stateCount)
    (hh : p.base.machine.halted c.control = false)
    (hq : p.query c.control = some rule)
    (hr : c.heads p.queryTape = 0)
    (hw : c.tapes p.queryTape = frame bits ++ padding) :
    OrdinaryOracleStep o (clocked p) ((frame bits).length + 1) (clockRecord c n)
      (clockRecord { c with control := if o (CanonicalBinary.bitsValue bits)
        then rule.onTrue else rule.onFalse } n) := by
  have hhalt : (clocked p).base.machine.halted (clockRecord c n).control = false := by
    simp [clocked, clockRecord, Rewind.machine, Rewind.recording, Rewind.config]
  have hquery : (clocked p).query (clockRecord c n).control = some (clockReturn rule) := by
    simp [clocked, clockRecord, Rewind.recording, Rewind.config, clockConfig, hh, hq]
  have hhead : (clockRecord c n).heads (clocked p).queryTape = 0 := by
    simpa [clocked, clockRecord, Rewind.recording, Rewind.config, clockConfig] using hr
  have htape : (clockRecord c n).tapes (clocked p).queryTape = frame bits ++ padding := by
    simpa [clocked, clockRecord, Rewind.recording, Rewind.config, clockConfig] using hw
  have h := OrdinaryOracleStep.ask (oracle := o) (program := clocked p) (clockRecord c n)
    bits padding (clockReturn rule) hhalt hquery hhead htape
  have he : (⟨(if o (CanonicalBinary.bitsValue bits)
      then (clockReturn rule).onTrue else (clockReturn rule).onFalse),
      (clockRecord c n).heads, (clockRecord c n).tapes⟩ : (clocked p).Config) =
      clockRecord { c with control := if o (CanonicalBinary.bitsValue bits)
        then rule.onTrue else rule.onFalse } n := by
    cases o (CanonicalBinary.bitsValue bits) <;> rfl
  rw [he] at h
  exact h

/-- The surviving unary clock counts local instructions only. Its value
bounds every head and every initially blank source tape. -/
theorem clock_trace {o : ℕ → Bool} {p : OrdinaryOracleProgram}
    {cost : ℕ} {c d : p.Config} (h : OrdinaryOracleTrace o p cost c d)
    (n : ℕ) (hh : ∀ i, c.heads i ≤ n)
    (caps : Fin p.base.tapeCount → ℕ)
    (ht : ∀ i, (c.tapes i).length ≤ max (caps i) n) :
    ∃ k, k ≤ cost ∧
      OrdinaryOracleTrace o (clocked p) cost (clockRecord c n) (clockRecord d (n + k)) ∧
      (∀ i, d.heads i ≤ n + k) ∧
      (∀ i, (d.tapes i).length ≤ max (caps i) (n + k)) := by
  induction h generalizing n with
  | refl c =>
    refine ⟨0, Nat.le_refl _, ?_, ?_, ?_⟩
    · simpa only [Nat.add_zero] using
        (OrdinaryOracleTrace.refl (oracle := o) (program := clocked p) (clockRecord c n))
    · simpa using hh
    · simpa using ht
  | @cons cost rest c middle d hs htail ih =>
    cases hs with
    | «local» c middle hhalt hquery hstep =>
      have hheads : ∀ i, middle.heads i ≤ n + 1 := by
        intro i
        exact (local_head_bound hstep i).trans (Nat.add_le_add_right (hh i) 1)
      have htapes : ∀ i, (middle.tapes i).length ≤ max (caps i) (n + 1) := by
        intro i
        have hb := local_tape_bound hstep i
        have ha := ht i
        have hp := hh i
        omega
      obtain ⟨k, hk, htr, hh', ht'⟩ := ih (n + 1) hheads htapes
      refine ⟨1 + k, by omega, ?_, ?_, ?_⟩
      · simpa only [Nat.add_assoc] using
          OrdinaryOracleTrace.cons (clock_local n hhalt hquery hstep) htr
      · simpa only [Nat.add_assoc] using hh'
      · simpa only [Nat.add_assoc] using ht'
    | ask c bits padding rule hhalt hquery hr hw =>
      obtain ⟨k, hk, htr, hh', ht'⟩ := ih n hh ht
      exact ⟨k, by omega, .cons (clock_ask c n bits padding rule hhalt hquery hr hw) htr,
        hh', ht'⟩

end NearCubicWires.RepairSource.OrdinaryOracleCompose
