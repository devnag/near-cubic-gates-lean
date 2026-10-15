import Proof.Gates.CheckedPCPP.Harness
import Proof.CaseAnalysis.CaseTwoRequestInput

set_option autoImplicit false

namespace NearCubicGates.Close.CheckedPCPP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.Bindings.CLW20Lemma311

/-- A circuit as a request with minimum arity `0`. -/
def circuitRequest (C : Circuit) : PCPPRequest 0 := ⟨C.n, C.D, Nat.zero_le _, C.sizeAtLeast⟩

theorem pcppInput_circuitRequest (C : Circuit) : pcppInput (circuitRequest C) = C.word := rfl

theorem word_run (C : Circuit) : ∃ out,
    ClockJoin.ReadyRun CloseoutCaseTwo.RequestInput.machine (CloseoutCaseTwo.RequestInput.budget C.D)
      (CloseoutCaseTwo.RequestInput.input (PCPPNative.descriptor C.D)) out ∧
      out CloseoutCaseTwo.RequestInput.outputSlot = frame C.word :=
  CloseoutCaseTwo.RequestInput.request_run (circuitRequest C)

end NearCubicGates.Close.CheckedPCPP
