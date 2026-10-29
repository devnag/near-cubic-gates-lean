import Proof.Gates.Main.Chain
import Proof.Gates.Interfaces.Transfer
import Proof.Gates.Interfaces.Counter
import Proof.Gates.Gadget.ThreeQuery
import Proof.Hierarchy.HierarchySourceConstructor
import Proof.MachineModel.ClockJoin
import Proof.PCP.PCPPNativeRequestSchema
import Proof.Wire_3_5.PrimTReadEq

set_option autoImplicit false

namespace NearCubicGates.Close.CheckedPCPP

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.WireExponent3_5.PrimT.ReadEq

/-- The supports record word (`imp:three-pcpp`: "Each systematic coordinate is a parity of input coordinates"):
code row `j < L` contributes `listWord natWord` of the canonical list of
its support (`canonList`, the order of `checkedCircuit`'s parity chains), as indices. -/
def supportsWord (E : LinearCodeFamily) (q : ℕ) : List Bool :=
  (List.finRange (E.length q)).flatMap fun j =>
    Interfaces.listWord natWord ((canonList (E.support q j)).map Fin.val)

/-- The composite's entry bank: `h` on the port `a`, `d` on the port `b`, every other tape empty. -/
def portBank (t : ℕ) (a b : Fin t) (h d : List Bool) : Fin t → List Bool :=
  fun i => if i = a then h else if i = b then d else []

/-- The word of the oracle circuit `C_{⟨B_src⟩_ν}` (`ν = log₂ N`) that the imported constructor returns (input 6's
`OracleOutput.word`; `sec:gadget-machine`, "It constructs `C^O_{⟨B_src⟩_ν}`"). -/
noncomputable def mwWord (s : GateSources) (g : GateParams) (N : ℕ)
    (Bsrc : BooleanCircuit (Outer.width s.mw (g.sv s) N)) : List Bool :=
  (Outer.outC s.mw (g.sv s) (Nat.log 2 N) Bsrc).word

/-- The outer verifier `D_B` of the guessed pair at source length `N` (the worker's `Worker.substituted`, the Case 2
producer's `D`; `sec:gadget-machine`, `D_B = ¬C^{O_{B_pf}}_{⟨B_src⟩_ν}` on `q` inputs). -/
noncomputable def substitutedAt (s : GateSources) (g : GateParams) {N : ℕ} (_x : BitInput N)
    (B : Outer.OuterGuess (Outer.width s.mw (g.sv s) N)) : Circuit :=
  Outer.Dat s.mw (g.sv s) (Nat.log 2 N) B

/-- The hierarchy word of the source instance `x` (kept for the recovery side's ports). -/
noncomputable def hierarchyWord (s : GateSources) (k : ℕ) (clock : OrdinaryClock (fun m => m ^ (k + 2)))
    {N : ℕ} (x : BitInput N) : List Bool :=
  HierarchySourceInput.hierarchyInput (s.hierarchy (fun m => m ^ (k + 2)) clock).hierarchy ⟨N, x⟩

def CompositeSpec : Prop :=
  ∀ (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams),
    ∃ (t st : ℕ) (M : LocalBitMultitape.Machine t st)
      (cIn dIn circuitOut wordOut supportsOut proofOut randomOut : Fin t) (C e : ℕ), cIn ≠ dIn ∧
      ∀ (N : ℕ) (x : BitInput N) (B : Outer.OuterGuess (Outer.width s.mw (g.sv s) N)),
        2 ≤ Outer.width s.mw (g.sv s) N →
        ∃ out, ClockJoin.ReadyRun M
            (C * ((mwWord s g N B.src).length + (PCPPNative.descriptor B.pf).length +
              Outer.width s.mw (g.sv s) N + 1) ^ e)
            (portBank t cIn dIn (mwWord s g N B.src) (PCPPNative.descriptor B.pf)) out ∧
          RdEq (out circuitOut) (RepairOrdinary.frame (checkedCircuit P.code (substitutedAt s g x B)).word) ∧
          RdEq (out wordOut) (P.output (checkedCircuit P.code (substitutedAt s g x B))).word ∧
          RdEq (out supportsOut) (RepairOrdinary.frame (supportsWord P.code (substitutedAt s g x B).n)) ∧
          RdEq (out proofOut)
            (RepairOrdinary.frame (P.output (checkedCircuit P.code (substitutedAt s g x B))).proofBits.bits) ∧
          RdEq (out randomOut)
            (RepairOrdinary.frame (P.output (checkedCircuit P.code (substitutedAt s g x B))).randomBits.bits)

end NearCubicGates.Close.CheckedPCPP
