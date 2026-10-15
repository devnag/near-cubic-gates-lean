import Proof.Hierarchy.CompetitorThresholdConstants

/-! The literal threshold decision with independently retained finite zero
padding on each tape. This transports the same physical transition run;
it neither creates padding nor assumes any extra arithmetic hypothesis. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMixedThreshold
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorThresholdDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (lower : Bool) (b p n d : ℕ) (q : ℚ) (pads : Fin 67 → ℕ) : Fin 67 → List Bool :=
  fun i => ZeroPadding.pad (pads i) (CompetitorThresholdDecision.input lower b p n d q i)

theorem threshold_run (lower : Bool) (b p n d : ℕ) (q : ℚ) (pads : Fin 67 → ℕ)
    (hp : p<2^b) (hn : n<2^b) (hd : d<2^b) (hdpos : 0<d)
    (hq : 0≤q) (hqnum : numerator q<2^b) (hqden : q.den<2^b) :
    ∃ out,ClockJoin.ReadyRun CompetitorRationalDecision.machine (2000*(b+1)^2)
      (input lower b p n d q pads) out ∧
      (readTapeBit (out 65) 0=true ↔ passes lower p n d q) := by
  obtain ⟨out,⟨base,hr,ht,hh,hs⟩,hflag⟩ := CompetitorThresholdDecision.threshold_run lower b p n d q
    hp hn hd hdpos hq hqnum hqden
  obtain ⟨r,hrun,hf,hsteps,_⟩ := ZeroPadding.run_config CompetitorRationalDecision.machine pads _ _ base hr
  refine ⟨r.final.tapes,⟨r,hrun,rfl,?_,hsteps.trans_le hs⟩,?_⟩
  · intro i
    rw [hf]
    exact hh i
  · simpa only [hf,ZeroPadding.config,ZeroPadding.read_pad,ht] using hflag

end NearCubicWires.RepairOrdinary.CompetitorMixedThreshold
