import Proof.Gates.Succinct.SubstitutionHeader
import Proof.Gates.Succinct.SubstitutionSpec

set_option autoImplicit false

namespace NearCubicGates.Close.Succinct.SubstMachine

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.Bindings.MW20
open NearCubicGates.Close.WordPrograms

/-- The cost class of one substitution. -/
def substCostClass (S : ℕ) : ℕ := 10000000000 * (S + 2) ^ 7

def SubstRunSpec : Prop :=
  ∀ (oc : OracleOutput) {q : ℕ} (B : BooleanCircuit q), ∃ (cap : ℕ) (τ : NearCubicWires.WireExponent3_5.FinalPass.Tm.WState 4 nrH),
    WXExec cap substProg (start oc.word (PCPPNative.descriptor B)) τ (substCostClass (sizeS oc B)) ∧
      τ.st sO = RepairOrdinary.frame (PCPPNative.descriptor (Outer.substCircuit oc.circuit B).padToArity) ∧
      τ.st sW = oc.word ∧ τ.st sD = PCPPNative.descriptor B

end NearCubicGates.Close.Succinct.SubstMachine
