import Proof.CaseAnalysis.FinalPipeline
import Proof.CaseAnalysis.FinalOnset
import Proof.CaseAnalysis.FinalAssembly

namespace NearCubicWires.RepairSource.CloseoutFinal

open RepairOrdinary RepairOrdinary.CloseoutWitness CompetitorRationalGap
open CompetitorSourceAverage AggregateSemanticStage SelectedRecoveryIntegration
open CloseoutLanguage SourceInterfaces RepairRepresentation SupplierPipeline
open CircuitRestriction

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! `Pipeline` unfolds to a nested `Σ'` over `pcppAt`/`req`/`outer`, which the
structure elaborator would `whnf` through at the 250000-heartbeat profile. It is
opaque here: the fusion is USED, never unfolded. No limit is raised. -/
attribute [local irreducible] C10Fusion.Pipeline

/-- The remaining physical obligations, with halting FUSED to semantics. -/
structure PhysicalWitnessC10 (sources : EightSources) (gamma : ℝ) where
  degree : Nat
  copies : Nat
  clauseDegree : Nat
  delta : ℚ
  symCap : ℝ
  thrCap : ℝ
  hdegree : 17*sources.amplification.stvExponent ≤ degree
  hcopies : (selectedAmplifier sources.amplification degree).arityCoefficient ≤ copies
  hD : 1 ≤ clauseDegree
  clauses : ClauseReady sources degree clauseDegree
  hd : 0 < delta
  hh : delta < 1/2
  heps : xorEpsilon (delta : ℝ) copies < gamma
  hsym : 0 < symCap
  hthr : 0 < thrCap
  k : Nat
  clock : OrdinaryClock (fun n => n^(k+2))
  tapes : Nat
  states : Nat
  worker : LocalBitMultitape.Machine tapes states
  htapes : 2 ≤ tapes
  result : Fin tapes
  fuel : Nat → Nat
  constants : Constants (selectedPCPP sources)
  /-- **The fusion.** `step` and `exposes` are both derived from this. -/
  pipeline : C10Fusion.Pipeline sources k clock constants worker htapes result fuel
  gateOnset : Nat
  /-- Paper C.10: the validity tolerance is fixed before the supplier accuracy,
  so `delta ≤ zeta constants`. -/
  hzeta : (delta : ℝ) ≤ ((zeta constants : ℚ) : ℝ)
  symDecides : SymDecidesFrom sources k clock constants worker htapes result fuel
    degree clauseDegree copies delta symCap gateOnset
  thrDecides : ThrDecidesFrom sources k clock constants worker htapes result fuel
    degree clauseDegree copies delta thrCap gateOnset
  A : Nat
  B : Nat
  a : Nat
  sigma : Nat
  hot : Nat → Nat
  ha : a ≤ k+1
  hsigma : 6+(fixedProjection sources).degrees.proofLog ≤ sigma
  splitOnset : Nat
  hpoly : ∀ N, splitOnset ≤ N → fuel N+2 ≤ A*(N+1)^a+hot N
  hdamp : ∀ N, splitOnset ≤ N →
    hot N*((outer sources k clock).result.pcp.nativeWidth N)^sigma ≤
      B*2^((outer sources k clock).result.pcp.nativeWidth N)

/-- Every fused witness is a `PhysicalWitness`; `step` and `exposes` come from the
one `pipeline`, and the two completeness fields from their onset-indexed forms. -/
def physicalWitness_of_C10 {sources : EightSources} {gamma : ℝ}
    (w : PhysicalWitnessC10 sources gamma) : PhysicalWitness sources gamma where
  degree := w.degree
  copies := w.copies
  clauseDegree := w.clauseDegree
  delta := w.delta
  symCap := w.symCap
  thrCap := w.thrCap
  hdegree := w.hdegree
  hcopies := w.hcopies
  hD := w.hD
  clauses := w.clauses
  hd := w.hd
  hh := w.hh
  heps := w.heps
  hsym := w.hsym
  hthr := w.hthr
  k := w.k
  clock := w.clock
  tapes := w.tapes
  states := w.states
  worker := w.worker
  htapes := w.htapes
  result := w.result
  budget := w.fuel
  fuel := w.fuel
  hfuel := fun _ => Nat.le_refl _
  step := C10Fusion.stepAtInputs_of_pipeline sources w.k w.clock w.pipeline
  constants := w.constants
  exposes := C10Fusion.exposes_of_pipeline sources w.k w.clock w.pipeline
  onsetSym := (encodesSym_of_symDecidesFrom sources w.k w.clock w.constants w.worker w.htapes
    w.result w.fuel w.degree w.clauseDegree w.copies w.delta w.symCap w.gateOnset
    w.hzeta w.symDecides).choose
  encodesSym := (encodesSym_of_symDecidesFrom sources w.k w.clock w.constants w.worker w.htapes
    w.result w.fuel w.degree w.clauseDegree w.copies w.delta w.symCap w.gateOnset
    w.hzeta w.symDecides).choose_spec
  onsetThr := (encodesThr_of_thrDecidesFrom sources w.k w.clock w.constants w.worker w.htapes
    w.result w.fuel w.degree w.clauseDegree w.copies w.delta w.thrCap w.gateOnset
    w.hzeta w.thrDecides).choose
  encodesThr := (encodesThr_of_thrDecidesFrom sources w.k w.clock w.constants w.worker w.htapes
    w.result w.fuel w.degree w.clauseDegree w.copies w.delta w.thrCap w.gateOnset
    w.hzeta w.thrDecides).choose_spec
  A := w.A
  B := w.B
  a := w.a
  sigma := w.sigma
  hot := w.hot
  ha := w.ha
  hsigma := w.hsigma
  splitOnset := w.splitOnset
  hpoly := w.hpoly
  hdamp := w.hdamp

/-- **The headline theorem from a fused witness.** -/
theorem theorem25_of_physicalC10
    (physical : (sources : EightSources) → ∀ gamma : ℝ, 0 < gamma → gamma < 1/2 →
      PhysicalWitnessC10 sources gamma)
    (sources : EightSources) : OrdinaryHeadlineTheorem25 :=
  theorem25_of_physical (fun s gamma hg hh => physicalWitness_of_C10 (physical s gamma hg hh)) sources

end
end NearCubicWires.RepairSource.CloseoutFinal
