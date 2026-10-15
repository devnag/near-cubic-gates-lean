import Proof.CaseAnalysis.WitnessMassReusableCheck
import Proof.CaseAnalysis.MassThresholdWidth

/-! The actual unchanged paper mass cap fits every produced witness policy.
Its complete ordinary check has no additional size guard or cutoff premise. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassActual
open LocalBitMultitape CompetitorSumFold
open CompetitorValidity (Estimate)
open RepairSource CloseoutMassThreshold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def width (delta : ℚ) (copies q0 clauseBits T : ℕ):=
  CompetitorSumWidth.width T
    (natBitLength (CloseoutXor.cap delta q0 copies*max 1 (2*2^clauseBits)))
def machine (delta : ℚ) (copies : ℕ):=
  MassCheck.machine (literalWidth delta copies) (CloseoutSampledWitness.massCap delta copies)
def budget (delta : ℚ) (copies q0 clauseBits T : ℕ):=
  MassCheck.budget (width delta copies q0 clauseBits T) (literalWidth delta copies)

theorem check_run (delta : ℚ) (hd : 0<delta) (hh : delta<1/2)
    (copies q0 clauseBits T : ℕ) (hc : 1≤copies) (a : Estimate) (source : List Bool)
    (ambient : Fin 94→List Bool)
    (h : Store (width delta copies q0 clauseBits T) a source ambient)
    (ha : a.Valid (width delta copies q0 clauseBits T)) : ∃ output,
    ClockJoin.ReadyRun (machine delta copies) (budget delta copies q0 clauseBits T)
      (MassCheck.input ambient) output ∧
      Store (width delta copies q0 clauseBits T) a source (CompetitorThresholdAmbient.project output) ∧
      (readTapeBit (output 65) 0=true ↔ a.value≤CloseoutSampledWitness.massCap delta copies):=by
  obtain ⟨_,hp,hden⟩:=threshold_fits delta hd hh copies q0 clauseBits hc
  exact MassReusableCheck.check_run (width delta copies q0 clauseBits T) (literalWidth delta copies)
    (CloseoutSampledWitness.massCap delta copies) a source ambient h ha
    (CloseoutSampledWitness.mass_nonneg delta hd hh copies)
    (shared_fits delta hd hh copies q0 clauseBits T hc) hp hden

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.MassActual
