import Proof.PCP.PCPPNativeHierarchyNodesInput
import Proof.PCP.PCPPNativeClauseQueryForward

/-! The complete original hierarchy/source/counter/node program writes
its descriptor-node output only by forward append. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeHierarchyNodes
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem counter_forward : CursorRestore.NoLeft PCPPNativeCounterNodes.machine 177 :=
  CursorRestore.composition_forward _ _ _
    (EquationRowRaw.embedded_extra_forward PCPPNativeColdCounters.machine (102 : Fin 363))
    (CursorRestore.focus_forward PCPPNativeCounterNodes.slots PCPPNativeCounterNodes.slots_injective
      _ 102 PCPPNativeClauseForward.whole)

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
theorem forward (k CH Cpad : ℕ) (code : List Bool) :
    CursorRestore.NoLeft (machine source k CH Cpad code) (slots source k 177) :=
  CursorRestore.composition_forward _ _ _
    (EquationRowRaw.embedded_extra_forward (PCPPNativeHierarchy.machine source k CH Cpad code) (177 : Fin 438))
    (CursorRestore.focus_forward (slots source k) (slots_injective source k) _ 177 counter_forward)

end NearCubicWires.RepairOrdinary.PCPPNativeHierarchyNodes
