import Proof.Foundations.ExecutableInterfaces
import StatementSupport

/-!
# Foundational finite-control local multitape bit machine

This lower-layer module is the source-facing machine model used by the
published Williams boundary and downstream loader.  A rule sees only the
current finite control state and the one scanned bit on each tape.  It writes
only those scanned cells and moves
each head by at most one position.  One rule application is one bit-TM step.

Unlike the earlier whole-configuration prototype, neither input loading nor an
arbitrary cost annotation is part of a transition.
-/

namespace NearCubicWires.LocalBitMultitape

theorem runFrom_zero_of_halted
    {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount)
    (configuration : Configuration tapeCount stateCount)
    (hhalted : machine.halted configuration.control = true) :
    runFrom machine 0 configuration =
      some
        { final := configuration
          steps := 0
          peakTapeCells := configuration.tapeCells } := by
  simp [runFrom, hhalted]

theorem runFrom_step
    {tapeCount stateCount fuel : ℕ}
    (machine : Machine tapeCount stateCount)
    (configuration next : Configuration tapeCount stateCount)
    (suffix : ExecutionReceipt tapeCount stateCount)
    (hnotHalted : machine.halted configuration.control = false)
    (hstep : step machine configuration = some next)
    (hsuffix : runFrom machine fuel next = some suffix) :
    runFrom machine (fuel + 1) configuration =
      some
        { final := suffix.final
          steps := suffix.steps + 1
          peakTapeCells := max configuration.tapeCells suffix.peakTapeCells } := by
  simp [runFrom, hnotHalted, hstep, hsuffix]

theorem applyAction_head_local
    {tapeCount stateCount : ℕ}
    (configuration : Configuration tapeCount stateCount)
    (action : Action tapeCount stateCount)
    (tape : Fin tapeCount) :
    (applyAction configuration action).heads tape =
      (action.move tape).apply (configuration.heads tape) :=
  rfl

theorem applyAction_tape_local
    {tapeCount stateCount : ℕ}
    (configuration : Configuration tapeCount stateCount)
    (action : Action tapeCount stateCount)
    (tape : Fin tapeCount) :
    (applyAction configuration action).tapes tape =
      match action.write tape with
      | none => configuration.tapes tape
      | some value =>
          writeTapeBit (configuration.tapes tape) (configuration.heads tape)
            value :=
  rfl

end NearCubicWires.LocalBitMultitape
