import Proof.Gates.GateRecovery.Aliases
import Proof.Foundations.SourceRegistry
import Proof.MachineModel.ClockJoin

namespace GR

set_option autoImplicit false

namespace NearCubicWires.RepairSource

open SourceInterfaces RepairRepresentation RepairOrdinary LocalBitMultitape

/-- The dyadic native widths and a machine printing them (`sec:gadget-machine` `q(N)`, `sec:all-lengths`
"bounded additive jumps"). -/
structure WidthSource where
  /-- `s ↦ q(N_s)`, `N_s = 2^s`. -/
  width : ℕ → ℕ
  jump : ℕ
  lower : ∀ s, s + 1 ≤ width s
  step : ∀ s, width (s + 1) ≤ width s + jump
  tapes : ℕ
  states : ℕ
  machine : Machine tapes states
  inPort : Fin tapes
  outPort : Fin tapes
  ports_ne : inPort ≠ outPort
  budget : ℕ → ℕ
  run : ∀ s, ∃ out, ClockJoin.ReadyRun machine (budget s)
    (fun i => if i = inPort then frame (List.replicate (2 ^ s) true) else []) out ∧
    out outPort = List.replicate (width s) true
  coefficient : ℕ
  degree : ℕ
  poly : ∀ s, budget s ≤ coefficient * (2 ^ s + 1) ^ degree

structure GateEightSources where
  normalization : ThresholdNormalizationContract
  width : WidthSource
  refuterXor : RefuterXorSourceGroup
  amplifier : Nonempty SourceAmplifierFactory

noncomputable def GateEightSources.hierarchy (sources : GateEightSources)
    (T : ℕ → ℕ) (clock : OrdinaryClock T) : HierarchyRefuterAlgorithm T :=
  Classical.choice (sources.refuterXor.hierarchyRefuter T clock)

noncomputable def GateEightSources.amplification (sources : GateEightSources) : SourceAmplifierFactory :=
  Classical.choice sources.amplifier

end NearCubicWires.RepairSource

end GR
