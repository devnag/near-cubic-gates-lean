import Proof.MachineModel.OrdinaryOracleComposeClock

/-! Closing the recorder with an executed rewind. The unary local-step
driver survives, and bounds the shared query tape before its later erase. -/
namespace NearCubicWires.RepairSource.OrdinaryOracleCompose
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem rewind_trace (o : ℕ → Bool) (p : OrdinaryOracleProgram)
    (heads : Fin (p.base.tapeCount + 1) → ℕ)
    (tapes : Fin (p.base.tapeCount + 1) → List Bool)
    (n z : ℕ) (hh : ∀ i, heads i ≤ n) :
    OrdinaryOracleTrace o (clocked p) (n + 1)
      (Rewind.rewinding (s := p.base.stateCount) heads tapes n z)
      (Rewind.finished (s := p.base.stateCount) tapes (n + z)) := by
  induction n generalizing heads z with
  | zero =>
    have hz : heads = fun _ => 0 := by funext i; have hi := hh i; omega
    subst heads
    have hs : OrdinaryOracleStep o (clocked p) 1
        (Rewind.rewinding (s := p.base.stateCount) (fun _ => 0) tapes 0 z)
        (Rewind.finished (s := p.base.stateCount) tapes z) := by
      refine .local _ _ ?_ ?_ (Rewind.finish_step (clockMachine p.base.machine) tapes z)
      · simp [clocked, Rewind.machine, Rewind.rewinding, Rewind.config]
      · simp [clocked, Rewind.rewinding, Rewind.config]
    simpa using single hs
  | succ n ih =>
    have hh' : ∀ i, heads i - 1 ≤ n := by intro i; have hi := hh i; omega
    have tail := ih (fun i => heads i - 1) (z + 1) hh'
    have hs : OrdinaryOracleStep o (clocked p) 1
        (Rewind.rewinding (s := p.base.stateCount) heads tapes (n + 1) z)
        (Rewind.rewinding (s := p.base.stateCount) (fun i => heads i - 1) tapes n (z + 1)) := by
      refine .local _ _ ?_ ?_ (Rewind.rewind_step (clockMachine p.base.machine) heads tapes n z)
      · simp [clocked, Rewind.machine, Rewind.rewinding, Rewind.config]
      · simp [clocked, Rewind.rewinding, Rewind.config]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      OrdinaryOracleTrace.cons hs tail

theorem reset_trace (o : ℕ → Bool) (p : OrdinaryOracleProgram)
    (c : p.Config) (n : ℕ) (hh : ∀ i, c.heads i ≤ n)
    (halted : p.base.machine.halted c.control = true) :
    OrdinaryOracleTrace o (clocked p) (n + 2) (clockRecord c n)
      (Rewind.finished (s := p.base.stateCount) (clockConfig c n).tapes n) := by
  have hc : ∀ i, (clockConfig c n).heads i ≤ n := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [clockConfig] using hh j
    · simp [clockConfig]
  have hs : OrdinaryOracleStep o (clocked p) 1 (clockRecord c n)
      (Rewind.rewinding (s := p.base.stateCount) (clockConfig c n).heads
        (clockConfig c n).tapes n 0) := by
    refine .local _ _ ?_ ?_ (Rewind.bridge_step (clockMachine p.base.machine)
      (clockConfig c n) n halted)
    · simp [clocked, clockRecord, Rewind.machine, Rewind.recording, Rewind.config]
    · simp [clocked, clockRecord, Rewind.recording, Rewind.config, clockConfig, halted]
  have ht := rewind_trace o p (clockConfig c n).heads (clockConfig c n).tapes n 0 hc
  simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    OrdinaryOracleTrace.cons hs ht

def clockTape (p : OrdinaryOracleProgram) : Fin (clocked p).base.tapeCount :=
  ((0 : Fin 1).natAdd p.base.tapeCount).castAdd 1

def resetTape (p : OrdinaryOracleProgram) : Fin (clocked p).base.tapeCount :=
  (0 : Fin 1).natAdd (p.base.tapeCount + 1)

theorem clock_initial (p : OrdinaryOracleProgram) (input : List Bool) :
    clockRecord (initialConfiguration p.base.machine (p.base.inputTapes input)) 0 =
      initialConfiguration (clocked p).base.machine ((clocked p).base.inputTapes input) := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
        simp [clockRecord, Rewind.recording, Rewind.config, clockConfig, initialConfiguration]
    · simp [clockRecord, Rewind.recording, Rewind.config, initialConfiguration]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simp [clockRecord, Rewind.recording, Rewind.config, clockConfig,
          initialConfiguration, Program.inputTapes]
      · have hp := p.base.twoTapes
        simp [clockRecord, Rewind.recording, Rewind.config, clockConfig,
          initialConfiguration, Program.inputTapes, show p.base.tapeCount ≠ 0 by omega]
    · simp [clockRecord, Rewind.recording, Rewind.config, initialConfiguration, Program.inputTapes]

/-- The wrapper supplies the endpoint needed by composition from the exact
source contract, without a source head-reset or workspace assumption. -/
theorem clocked_runs {o : ℕ → Bool} {p : OrdinaryOracleProgram}
    {input output : List Bool} {budget : ℕ}
    (h : OrdinaryOracleRuns o p input output budget) :
    ∃ cost n final, cost ≤ budget ∧ n ≤ cost ∧
      OrdinaryOracleTrace o (clocked p) (cost + n + 2)
        (initialConfiguration (clocked p).base.machine ((clocked p).base.inputTapes input)) final ∧
      (clocked p).base.machine.halted final.control = true ∧
      final.tapes (clocked p).base.outputTape = frame output ∧
      (∀ i, final.heads i = 0) ∧
      final.tapes (clockTape p) = List.replicate n true ∧
      final.tapes (resetTape p) = List.replicate n false ∧
      (final.tapes (clocked p).queryTape).length ≤ n ∧
      (frame output).length ≤ n := by
  obtain ⟨cost, source, hc, htrace, hh, hout⟩ := h
  obtain ⟨n, hn, hrecord, hheads, htapes⟩ := clock_trace htrace 0
    (by simp [initialConfiguration]) (fun i => (p.base.inputTapes input i).length)
    (by simp [initialConfiguration])
  simp only [Nat.zero_add] at hrecord hheads htapes
  let final := Rewind.finished (s := p.base.stateCount) (clockConfig source n).tapes n
  refine ⟨cost, n, final, hc, hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have joined := trans hrecord (reset_trace o p source n hheads hh)
    rw [clock_initial] at joined
    simpa only [Nat.add_assoc] using joined
  · simp [final, clocked, Rewind.finished, Rewind.config, Rewind.machine]
  · simpa [final, clocked, Rewind.finished, Rewind.config, clockConfig] using hout
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [final, Rewind.finished, Rewind.config]
  · simp [final, clockTape, Rewind.finished, Rewind.config, clockConfig]
  · simp [final, resetTape, Rewind.finished, Rewind.config]
  · simpa [final, clocked, Rewind.finished, Rewind.config, clockConfig,
      Program.inputTapes, p.queryFresh] using htapes p.queryTape
  · have ho := htapes p.base.outputTape
    simpa [Program.inputTapes, p.base.outputFresh, hout] using ho

end NearCubicWires.RepairSource.OrdinaryOracleCompose
