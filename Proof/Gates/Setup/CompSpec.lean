import Proof.Gates.CheckedPCPP.Composite

set_option autoImplicit false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.Close NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Transfer

/-- The composite with exact outputs, the supports port included ((a′) form). -/
structure CompFull (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) where
  t : ℕ
  st : ℕ
  M : Machine t st
  cIn : Fin t
  dIn : Fin t
  cOut : Fin t
  wOut : Fin t
  sOut : Fin t
  pOut : Fin t
  rOut : Fin t
  C : ℕ
  e : ℕ
  nd : [cIn, dIn, cOut, wOut, sOut, pOut, rOut].Nodup
  run : ∀ {N : ℕ} (x : BitInput N) (B : Outer.OuterGuess (Outer.width s.mw (g.sv s) N)),
    2 ≤ Outer.width s.mw (g.sv s) N →
    ∃ out, ClockJoin.ReadyRun M (C * ((mwWord s g N B.src).length + (PCPPNative.descriptor B.pf).length +
        Outer.width s.mw (g.sv s) N + 1) ^ e)
      (portBank t cIn dIn (mwWord s g N B.src) (PCPPNative.descriptor B.pf)) out ∧
      out cOut = RepairOrdinary.frame (checkedCircuit P.code (substitutedAt s g x B)).word ∧
      out wOut = (P.output (checkedCircuit P.code (substitutedAt s g x B))).word ∧
      out sOut = RepairOrdinary.frame (supportsWord P.code (substitutedAt s g x B).n) ∧
      out pOut = RepairOrdinary.frame (P.output (checkedCircuit P.code (substitutedAt s g x B))).proofBits.bits ∧
      out rOut = RepairOrdinary.frame (P.output (checkedCircuit P.code (substitutedAt s g x B))).randomBits.bits

end NearCubicGates.Close.Setup
