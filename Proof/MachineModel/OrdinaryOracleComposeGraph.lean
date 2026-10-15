import Proof.MachineModel.OrdinaryOracleComposeReset
import Proof.Amplification.RecoveryCallController
import Proof.Amplification.RecoveryFocusedMachine

/-! The compositor's finite call graph. All pieces share one oracle port;
source queries and their literal costs survive static tape/control wiring. -/
namespace NearCubicWires.RepairSource.OrdinaryOracleCompose
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Ports (t : ℕ) where
  twoTapes : 2 ≤ t
  outputTape : Fin t
  outputFresh : outputTape.val ≠ 0
  queryTape : Fin t
  queryFresh : queryTape.val ≠ 0

structure Piece (t : ℕ) where
  states : ℕ
  machine : Machine t states
  query : Fin states → Option (OracleReturn states)

abbrev Ports.program {t : ℕ} (ports : Ports t) (p : Piece t) : OrdinaryOracleProgram where
  base := ⟨t, p.states, ports.twoTapes, p.machine, ports.outputTape, ports.outputFresh⟩
  queryTape := ports.queryTape
  queryFresh := ports.queryFresh
  query := p.query

noncomputable abbrev focused {t : ℕ} (p : OrdinaryOracleProgram)
    (slot : Fin p.base.tapeCount → Fin t) : Piece t :=
  ⟨p.base.stateCount, RecoveryFocus.machine slot p.base.machine, p.query⟩

theorem focus_trace {o : ℕ → Bool} {p : OrdinaryOracleProgram} {t : ℕ}
    (ports : Ports t) (slot : Fin p.base.tapeCount → Fin t)
    (hi : Function.Injective slot) (hq : slot p.queryTape = ports.queryTape)
    (heads : Fin t → ℕ) (tapes : Fin t → List Bool)
    {cost : ℕ} {c d : p.Config} (h : OrdinaryOracleTrace o p cost c d) :
    OrdinaryOracleTrace o (ports.program (focused p slot)) cost
      (RecoveryFocus.config slot heads tapes c) (RecoveryFocus.config slot heads tapes d) := by
  induction h with
  | refl => exact .refl _
  | @cons cost rest c middle d hs ht ih =>
    apply OrdinaryOracleTrace.cons (program := ports.program (focused p slot))
      (middle := RecoveryFocus.config slot heads tapes middle) _ ih
    cases hs with
    | «local» c middle hh hquery hstep =>
      refine .local _ _ hh hquery ?_
      change step (RecoveryFocus.machine slot p.base.machine)
        (RecoveryFocus.config slot heads tapes c) = _
      rw [RecoveryFocus.step_config slot hi, hstep]
      rfl
    | ask c bits padding rule hh hquery hr hw =>
      have hhead : (RecoveryFocus.config slot heads tapes c).heads ports.queryTape = 0 := by
        rw [← hq]
        simpa [RecoveryFocus.config, RecoveryFocus.pick_slot slot hi] using hr
      have htape : (RecoveryFocus.config slot heads tapes c).tapes ports.queryTape =
          frame bits ++ padding := by
        rw [← hq]
        simpa [RecoveryFocus.config, RecoveryFocus.pick_slot slot hi] using hw
      have ha := OrdinaryOracleStep.ask (oracle := o)
        (program := ports.program (focused p slot)) (RecoveryFocus.config slot heads tapes c)
        bits padding rule hh hquery hhead htape
      exact ha

noncomputable def callReturn {t k : ℕ} (pieces : Fin k → Piece t)
    (j : Fin k) (r : OracleReturn (pieces j).states) :
    OracleReturn (Fintype.card (RecoveryCalls.Control (fun j => (pieces j).states))) :=
  ⟨RecoveryCalls.code (fun j => (pieces j).states) j r.onFalse,
    RecoveryCalls.code (fun j => (pieces j).states) j r.onTrue⟩

noncomputable abbrev graph {t k : ℕ} (pieces : Fin k → Piece t) (entry : Fin k)
    (next : (j : Fin k) → Fin (pieces j).states → (Fin t → Bool) → Option (Fin k)) : Piece t where
  states := Fintype.card (RecoveryCalls.Control (fun j => (pieces j).states))
  machine := RecoveryCalls.machine (fun j => (pieces j).states) (fun j => (pieces j).machine) entry next
  query := fun state => match (RecoveryCalls.controlCode (fun j => (pieces j).states)).symm state with
    | none => none
    | some ⟨j, q⟩ => if (pieces j).machine.halted q then none
      else ((pieces j).query q).map (callReturn pieces j)

theorem graph_trace {o : ℕ → Bool} {t k : ℕ} (ports : Ports t)
    (pieces : Fin k → Piece t) (entry : Fin k)
    (next : (j : Fin k) → Fin (pieces j).states → (Fin t → Bool) → Option (Fin k))
    (j : Fin k) {cost : ℕ} {c d : (ports.program (pieces j)).Config}
    (h : OrdinaryOracleTrace o (ports.program (pieces j)) cost c d) :
    OrdinaryOracleTrace o (ports.program (graph pieces entry next)) cost
      (controlConfig (RecoveryCalls.code (fun j => (pieces j).states) j) c)
      (controlConfig (RecoveryCalls.code (fun j => (pieces j).states) j) d) := by
  induction h with
  | refl => exact .refl _
  | @cons cost rest c middle d hs ht ih =>
    apply OrdinaryOracleTrace.cons (program := ports.program (graph pieces entry next))
      (middle := controlConfig (RecoveryCalls.code (fun j => (pieces j).states) j) middle) _ ih
    cases hs with
    | «local» c middle hh hquery hstep =>
      refine .local _ _ ?_ ?_ ?_
      · simp [Ports.program, graph, RecoveryCalls.machine, controlConfig, RecoveryCalls.code]
      · change (graph pieces entry next).query (RecoveryCalls.code (fun j => (pieces j).states) j c.control) = none
        simp [graph, RecoveryCalls.code, show (pieces j).machine.halted c.control = false from hh,
          show (pieces j).query c.control = none from hquery]
      · exact RecoveryCalls.body_step _ _ entry next j c middle hh hstep
    | ask c bits padding rule hh hquery hr hw =>
      have hhalt : (ports.program (graph pieces entry next)).base.machine.halted
          (controlConfig (RecoveryCalls.code (fun j => (pieces j).states) j) c).control = false := by
        simp [Ports.program, graph, RecoveryCalls.machine, controlConfig, RecoveryCalls.code]
      have hq : (ports.program (graph pieces entry next)).query
          (controlConfig (RecoveryCalls.code (fun j => (pieces j).states) j) c).control =
          some (callReturn pieces j rule) := by
        simp [Ports.program, graph, controlConfig, RecoveryCalls.code,
          show (pieces j).machine.halted c.control = false from hh,
          show (pieces j).query c.control = some rule from hquery]
      have ha := OrdinaryOracleStep.ask (oracle := o)
        (program := ports.program (graph pieces entry next))
        (controlConfig (RecoveryCalls.code (fun j => (pieces j).states) j) c)
        bits padding (callReturn pieces j rule) hhalt hq hr hw
      have he : (⟨(if o (CanonicalBinary.bitsValue bits)
          then (callReturn pieces j rule).onTrue else (callReturn pieces j rule).onFalse),
          (controlConfig (RecoveryCalls.code (fun j => (pieces j).states) j) c).heads,
          (controlConfig (RecoveryCalls.code (fun j => (pieces j).states) j) c).tapes⟩ :
          (ports.program (graph pieces entry next)).Config) =
          controlConfig (RecoveryCalls.code (fun j => (pieces j).states) j)
            { c with control := if o (CanonicalBinary.bitsValue bits) then rule.onTrue else rule.onFalse } := by
        cases o (CanonicalBinary.bitsValue bits) <;> rfl
      exact Eq.mp (congrArg (fun endpoint : (ports.program (graph pieces entry next)).Config =>
        OrdinaryOracleStep o (ports.program (graph pieces entry next)) ((frame bits).length + 1)
          (controlConfig (RecoveryCalls.code (fun j => (pieces j).states) j) c) endpoint) he) ha

theorem graph_return (o : ℕ → Bool) {t k : ℕ} (ports : Ports t)
    (pieces : Fin k → Piece t) (entry : Fin k)
    (next : (j : Fin k) → Fin (pieces j).states → (Fin t → Bool) → Option (Fin k))
    (j l : Fin k) (c : Configuration t (pieces j).states)
    (hh : (pieces j).machine.halted c.control = true) (hn : next j c.control c.scanned = some l) :
    OrdinaryOracleTrace o (ports.program (graph pieces entry next)) 1
      (controlConfig (RecoveryCalls.code (fun j => (pieces j).states) j) c)
      (controlConfig (RecoveryCalls.code (fun j => (pieces j).states) l)
        (RecoveryCalls.restarted (pieces l).machine c.heads c.tapes)) := by
  apply single
  refine .local _ _ ?_ ?_ (RecoveryCalls.return_step _ _ entry next j l c hh hn)
  · simp [Ports.program, graph, RecoveryCalls.machine, controlConfig, RecoveryCalls.code]
  · simp [Ports.program, graph, controlConfig, RecoveryCalls.code, hh]

theorem graph_stop (o : ℕ → Bool) {t k : ℕ} (ports : Ports t)
    (pieces : Fin k → Piece t) (entry : Fin k)
    (next : (j : Fin k) → Fin (pieces j).states → (Fin t → Bool) → Option (Fin k))
    (j : Fin k) (c : Configuration t (pieces j).states)
    (hh : (pieces j).machine.halted c.control = true) (hn : next j c.control c.scanned = none) :
    OrdinaryOracleTrace o (ports.program (graph pieces entry next)) 1
      (controlConfig (RecoveryCalls.code (fun j => (pieces j).states) j) c)
      (RecoveryCalls.stopped (fun j => (pieces j).states) c.heads c.tapes) := by
  apply single
  refine .local _ _ ?_ ?_ (RecoveryCalls.stop_step _ _ entry next j c hh hn)
  · simp [Ports.program, graph, RecoveryCalls.machine, controlConfig, RecoveryCalls.code]
  · simp [Ports.program, graph, controlConfig, RecoveryCalls.code, hh]

abbrev ordinary {t s : ℕ} (p : Machine t s) : Piece t := ⟨s, p, fun _ => none⟩

theorem ordinary_trace {o : ℕ → Bool} {t s : ℕ} (ports : Ports t)
    (p : Machine t s) (fuel : ℕ) (c : Configuration t s) (r : ExecutionReceipt t s)
    (hr : runFrom p fuel c = some r) :
    OrdinaryOracleTrace o (ports.program (ordinary p)) r.steps c r.final := by
  induction fuel generalizing c r with
  | zero =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; exact .refl _
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; exact .refl _
    · next hh =>
      cases hs : step p c with
      | none => simp [hs] at hr
      | some d =>
        cases ht : runFrom p fuel d with
        | none => simp [hs, ht] at hr
        | some tail =>
          simp only [hs, ht, Option.some.injEq] at hr
          subst r
          have hlocal : OrdinaryOracleStep o (ports.program (ordinary p)) 1 c d :=
            OrdinaryOracleStep.local (program := ports.program (ordinary p)) c d
              (by simpa [Ports.program, ordinary] using hh) rfl hs
          simpa only [Nat.add_comm] using OrdinaryOracleTrace.cons hlocal (ih d tail ht)

end NearCubicWires.RepairSource.OrdinaryOracleCompose
