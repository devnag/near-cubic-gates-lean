import Proof.Gates.CheckedPCPP.Composite

set_option autoImplicit false

namespace NearCubicGates.Close.Succinct.SubstMachine

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.Bindings.MW20

def SubstReadySpec : Prop :=
  ∃ (t st : ℕ) (M : LocalBitMultitape.Machine t st) (iW iD o : Fin t) (K e : ℕ),
    [iW, iD, o].Nodup ∧
    ∀ (oc : OracleOutput) {q : ℕ} (B : BooleanCircuit q),
      ∃ out, ClockJoin.ReadyRun M (K * (oc.word.length + (PCPPNative.descriptor B).length + q + 1) ^ e)
          (CheckedPCPP.portBank t iW iD oc.word (PCPPNative.descriptor B)) out ∧
        out o = RepairOrdinary.frame (PCPPNative.descriptor (Outer.substCircuit oc.circuit B).padToArity) ∧
        out iW = oc.word ∧ out iD = PCPPNative.descriptor B

end NearCubicGates.Close.Succinct.SubstMachine
