import Proof.CaseAnalysis.FinalClose

namespace NearCubicWires.RepairSource.CloseoutFinal

open RepairOrdinary RepairOrdinary.CloseoutWitness CompetitorRationalGap
open CompetitorSourceAverage AggregateSemanticStage SelectedRecoveryIntegration
open CloseoutLanguage SourceInterfaces RepairRepresentation SupplierPipeline
open CircuitRestriction CloseoutParameters

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

attribute [local irreducible] C10Fusion.Pipeline SymDecidesFrom ThrDecidesFrom

/-- The completion shape of Theorem 2.5 on this route: the eight corrected sources
give the ordinary headline. -/
abbrev Theorem25Target : Prop := ∀ _ : EightSources, OrdinaryHeadlineTheorem25

structure Parameters (sources : EightSources) (gamma : ℝ) where
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

structure Machine (sources : EightSources) (degree clauseDegree copies : Nat) where
  k : Nat
  clock : OrdinaryClock (fun n => n^(k+2))
  tapes : Nat
  states : Nat
  worker : LocalBitMultitape.Machine tapes states
  htapes : 2 ≤ tapes
  result : Fin tapes
  fuel : Nat → Nat
  pipeline : C10Fusion.Pipeline sources k clock (constantsOf sources) worker htapes result fuel
  gateOnset : Nat
  symCap : ℝ
  thrCap : ℝ
  hsym : 0 < symCap
  hthr : 0 < thrCap
  symDecides : SymDecidesFrom sources k clock (constantsOf sources) worker htapes result fuel
    degree clauseDegree copies (zeta (constantsOf sources)) symCap gateOnset
  thrDecides : ThrDecidesFrom sources k clock (constantsOf sources) worker htapes result fuel
    degree clauseDegree copies (zeta (constantsOf sources)) thrCap gateOnset

structure Runtime (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2)))
    (fuel : Nat → Nat) where
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

def residual_of_leaves {sources : EightSources} {gamma : ℝ}
    (p : Parameters sources gamma) (m : Machine sources p.degree p.clauseDegree p.copies)
    (r : Runtime sources m.k m.clock m.fuel) : Residual sources gamma where
  degree := p.degree
  copies := p.copies
  clauseDegree := p.clauseDegree
  hdegree := p.hdegree
  hcopies := p.hcopies
  hD := p.hD
  clauses := p.clauses
  hd := p.hd
  hh := p.hh
  heps := p.heps
  symCap := m.symCap
  thrCap := m.thrCap
  hsym := m.hsym
  hthr := m.hthr
  k := m.k
  clock := m.clock
  tapes := m.tapes
  states := m.states
  worker := m.worker
  htapes := m.htapes
  result := m.result
  fuel := m.fuel
  pipeline := m.pipeline
  gateOnset := m.gateOnset
  symDecides := m.symDecides
  thrDecides := m.thrDecides
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

theorem parameters_of_sources (sources : EightSources) (gamma : ℝ) (hg : 0 < gamma) :
    Nonempty (Parameters sources gamma) := by
  obtain ⟨degree, copies, clauseDegree, hdegree, hcopies, hD, clauses, hd, hh, heps⟩ :=
    exists_closureParametersZeta sources (constantsOf sources) gamma hg
  exact ⟨⟨degree, copies, clauseDegree, hdegree, hcopies, hD, clauses, hd, hh, heps⟩⟩

theorem theorem25_of_leaves
    (machine : (sources : EightSources) → ∀ gamma : ℝ, 0 < gamma → gamma < 1/2 →
      (p : Parameters sources gamma) → Machine sources p.degree p.clauseDegree p.copies)
    (runtime : (sources : EightSources) → ∀ gamma : ℝ, ∀ hg : 0 < gamma, ∀ hh : gamma < 1/2,
      (p : Parameters sources gamma) →
      Runtime sources (machine sources gamma hg hh p).k (machine sources gamma hg hh p).clock
        (machine sources gamma hg hh p).fuel) :
    Theorem25Target := fun sources =>
  theorem25_of_residual
    (fun s gamma hg hh =>
      let p := Classical.choice (parameters_of_sources s gamma hg)
      residual_of_leaves p (machine s gamma hg hh p) (runtime s gamma hg hh p))
    sources

end NearCubicWires.RepairSource.CloseoutFinal
