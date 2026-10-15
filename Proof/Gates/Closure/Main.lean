import Proof.Gates.Closure.ClauseRoom
import Proof.Gates.Closure.Asymptotics
import Proof.Gates.Transfer.RecoveryTarget
import Proof.Gates.Main.Application
import Proof.Gates.Succinct.Main

/-!
# The main theorem from the remaining machine obligations ((a′) repair)

`FinalStatement` (nine inputs ⇒ the paper's main theorem) follows from exactly three named obligations, each a
machine whose type names the quantity paper v2 asks it to compute:
* `CounterSupply` — the counter of thm:pair-uniform as one ordinary program;
* `WorkerSupply` — the weak machine of §11.4 deciding `Worker.Meaning` (guess = the pair `(B_src, B_pf)`, CHECK, the
  outer verifier `D_B` of the imported short PCP applied to `𝒱_G`), with its runtime split;
* `Transfer.RecoverySupply` — the padded native family in `E^NP` (§11.6, the three SAT stages of the canonical
  choices).
lem:succinct-verifier is proved (`Succinct.succinctVerifier_exists`) and supplied here.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Closure

open NearCubicGates.Close.Transfer

/-- lem:succinct-verifier for every clock. -/
theorem succinctSupply : Outer.SuccinctSupply :=
  fun _k H G => Succinct.succinctVerifier_exists H G

/-- The weak-machine side modulo its two machines. -/
theorem closureSupply_of_machines (hC : CounterSupply) (hW : WorkerSupply) : ClosureSupply :=
  closureSupply_of hC hW asymptoticsFacts clauseRoom

/-- **The main theorem modulo the three machine obligations**: the counter program, the worker machine, and the
`E^NP` recovery of the padded native family. -/
theorem final_of_machines (hC : CounterSupply) (hW : WorkerSupply) (hR : RecoverySupply) :
    NearCubicGates.Close.FinalStatement :=
  main_from_inputs_of_frontier (frontierSupply_of_recoverySupply hR (closureSupply_of_machines hC hW)) succinctSupply

end NearCubicGates.Close.Closure
