import Proof.CaseAnalysis.FinalAssemblyFused
import Proof.CaseAnalysis.FinalParametersZeta

namespace NearCubicWires.RepairSource.CloseoutFinal

open RepairOrdinary RepairOrdinary.CloseoutWitness CompetitorRationalGap
open CompetitorSourceAverage AggregateSemanticStage SelectedRecoveryIntegration
open CloseoutLanguage SourceInterfaces RepairRepresentation SupplierPipeline
open CircuitRestriction CloseoutParameters

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! The residual's field types mention `Pipeline`, `SymDecidesFrom`,
`ThrDecidesFrom` and `constantsOf`, each of which unfolds through `pcppAt`,
`req`, `outer` or a `Classical.choice`. The structure elaborator would `whnf`
through all of them at the 250000-heartbeat profile. They are opaque here: USED,
never unfolded. No limit is raised. -/
attribute [local irreducible] C10Fusion.Pipeline SymDecidesFrom ThrDecidesFrom

/-- The validity tolerance, fixed before the supplier accuracy (paper freeze
order, paper.tex:474). Free from the eight sources. -/
irreducible_def constantsOf (sources : EightSources) : Constants (selectedPCPP sources) :=
  Classical.choice (constants_exist (selectedPCPP sources))

/-- **The residual physical obligation, in full.** Nothing else stands between
the eight sources and the headline theorem. -/
structure Residual (sources : EightSources) (gamma : ℝ) where
  degree : Nat
  copies : Nat
  clauseDegree : Nat
  hdegree : 17*sources.amplification.stvExponent ≤ degree
  hcopies : (selectedAmplifier sources.amplification degree).arityCoefficient ≤ copies
  hD : 1 ≤ clauseDegree
  clauses : ClauseReady sources degree clauseDegree
  hd : 0 < zeta (constantsOf sources)
  hh : zeta (constantsOf sources) < 1/2
  heps : xorEpsilon ((zeta (constantsOf sources) : ℚ) : ℝ) copies < gamma
  symCap : ℝ
  thrCap : ℝ
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
  /-- Paper C.10 at every length, halting FUSED to semantics. -/
  pipeline : C10Fusion.Pipeline sources k clock (constantsOf sources) worker htapes result fuel
  gateOnset : Nat
  symDecides : SymDecidesFrom sources k clock (constantsOf sources) worker htapes result fuel
    degree clauseDegree copies (zeta (constantsOf sources)) symCap gateOnset
  thrDecides : ThrDecidesFrom sources k clock (constantsOf sources) worker htapes result fuel
    degree clauseDegree copies (zeta (constantsOf sources)) thrCap gateOnset
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

/-- A residual is a fused physical witness, at `delta := zeta constants`. -/
def physicalWitness_of_residual {sources : EightSources} {gamma : ℝ}
    (r : Residual sources gamma) : PhysicalWitnessC10 sources gamma where
  degree := r.degree
  copies := r.copies
  clauseDegree := r.clauseDegree
  delta := zeta (constantsOf sources)
  symCap := r.symCap
  thrCap := r.thrCap
  hdegree := r.hdegree
  hcopies := r.hcopies
  hD := r.hD
  clauses := r.clauses
  hd := r.hd
  hh := r.hh
  heps := r.heps
  hsym := r.hsym
  hthr := r.hthr
  k := r.k
  clock := r.clock
  tapes := r.tapes
  states := r.states
  worker := r.worker
  htapes := r.htapes
  result := r.result
  fuel := r.fuel
  constants := constantsOf sources
  pipeline := r.pipeline
  gateOnset := r.gateOnset
  hzeta := le_refl _
  symDecides := r.symDecides
  thrDecides := r.thrDecides
  A := r.A
  B := r.B
  a := r.a
  sigma := r.sigma
  hot := r.hot
  ha := r.ha
  hsigma := r.hsigma
  splitOnset := r.splitOnset
  hpoly := r.hpoly
  hdamp := r.hdamp

/-- **THE CLOSE.** The eight sources give paper Theorem 2.5 once the residual
physical witness exists. -/
theorem theorem25_of_residual
    (residual : (sources : EightSources) → ∀ gamma : ℝ, 0 < gamma → gamma < 1/2 →
      Residual sources gamma)
    (sources : EightSources) : OrdinaryHeadlineTheorem25 :=
  theorem25_of_physicalC10
    (fun s gamma hg hh => physicalWitness_of_residual (residual s gamma hg hh)) sources

end
end NearCubicWires.RepairSource.CloseoutFinal
