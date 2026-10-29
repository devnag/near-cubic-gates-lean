import Proof.MachineModel.OrdinaryOracleCompose
import Proof.MachineModel.OrdinaryControlPrefix
import Proof.Foundations.OrdinaryRewindCarrier

/-!
# Single-run time, machine layer 3: ordinary stages of an oracle program

The single-run verifier (proof of `thm:short-pcp-ours`: "consider the computation of V1 … its proof bits are read at addresses below
L_π") is built as a chain of stages composed with the released `OrdinaryOracleCompose.compose_runs`: ordinary word
functions (no oracle queries; proof of `thm:short-pcp-ours`, "The queries of V0 are computed from the random string alone") around one
oracle-reading stage. This module turns an ordinary program into an oracle program with no queries: a word function
whose output word is `frame u` runs, as an oracle program, with output `u` (`oracleOfProgram_runs`), within its budget.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Machines

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.OrdinaryOracleCompose

/-- The ports of an ordinary program: output and (never used) query tape both on its output tape. -/
def wordPorts (p : Program) : Ports p.tapeCount :=
  ⟨p.twoTapes, p.outputTape, p.outputFresh, p.outputTape, p.outputFresh⟩

/-- **An ordinary program as an oracle program** with no queries. -/
noncomputable def oracleOfProgram (p : Program) : OrdinaryOracleProgram :=
  (wordPorts p).program (ordinary p.machine)

/-- **A word function with framed output runs as an oracle program** (any oracle, within its budget). -/
theorem oracleOfProgram_runs {Req : Type} {input output : Req → List Bool} {budget : Req → ℕ}
    (wf : WordFunction Req input output budget) (o : ℕ → Bool) (r : Req) (u : List Bool)
    (hu : output r = RepairOrdinary.frame u) :
    OrdinaryOracleRuns o (oracleOfProgram wf.program) (input r) u (budget r) := by
  obtain ⟨rc, hrc, hout⟩ := wf.realizes r
  refine ⟨rc.steps, rc.final, runFrom_steps_le _ _ _ _ hrc, ?_, (prefix_of_run _ _ _ _ hrc).2, ?_⟩
  · exact ordinary_trace (o := o) (wordPorts wf.program) wf.program.machine (budget r) _ rc hrc
  · show rc.final.tapes wf.program.outputTape = RepairOrdinary.frame u
    rw [hout, hu]

/-- **Four stages composed** (`compose_runs` three times). -/
theorem compose4_runs {o : ℕ → Bool} {p1 p2 p3 p4 : OrdinaryOracleProgram} {w0 w1 w2 w3 w4 : List Bool}
    {b1 b2 b3 b4 : ℕ} (h1 : OrdinaryOracleRuns o p1 w0 w1 b1) (h2 : OrdinaryOracleRuns o p2 w1 w2 b2)
    (h3 : OrdinaryOracleRuns o p3 w2 w3 b3) (h4 : OrdinaryOracleRuns o p4 w3 w4 b4) :
    OrdinaryOracleRuns o (compose (compose (compose p1 p2) p3) p4) w0 w4
      (16 * (16 * (16 * (b1 + b2 + 1) + b3 + 1) + b4 + 1)) :=
  compose_runs (compose_runs (compose_runs h1 h2) h3) h4

end NearCubicGates.Adapters.ShortPCP.Machines
