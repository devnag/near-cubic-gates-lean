import Proof.CaseAnalysis.FinalCompletenessDyadic
import Proof.CaseAnalysis.FinalOneSidedness
import Proof.CaseAnalysis.FinalSupplierStepBridge
import Proof.CaseAnalysis.HardnessPremises

/-! The assembly seat.

`ClosureAt` asks for four obligations whose content is mathematical:
`supplier`, `sound`, `complSym`/`complThr` and `split`. Each has already been
reduced, in its own module and against the paper, to a *physical* statement:

* `supplier`  -> `Weak.StepAtInputs`  : the assembled worker halts, docked at
  the verifier's own input tapes (`SupplierStepBridge`, paper C.10).
* `sound`     -> `Exposes`            : the accuracy facts (`SoundnessBind`).
* `complSym`/`complThr` -> `EncodesSym`/`EncodesThr` : the encoder
  (`CompletenessBind`, paper C.10 dyadic completeness).
* `split`     -> one polynomial bound and one damping bound (paper A.7/A.8).

`PhysicalWitness` is exactly that list, and nothing else. It fixes the shape of
the remaining work: no further mathematics stands between it and the headline
theorem, only the physical receipts themselves. -/
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

structure PhysicalWitness (sources : EightSources) (gamma : ℝ) where
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
  budget : Nat → Nat
  fuel : Nat → Nat
  hfuel : ∀ n, budget n ≤ fuel n
  /-- Paper C.10: the worker halts inside its own budget on every input. -/
  step : Weak.StepAtInputs worker htapes result budget
  constants : Constants (selectedPCPP sources)
  /-- Paper C.12: the accuracy facts exposed by an accepted run. -/
  exposes : Exposes sources k clock constants
    (Weak.decides worker htapes result fuel)
  onsetSym : Nat
  /-- Paper C.10: an honest symmetric family is encodable as an accepted witness. -/
  encodesSym : EncodesSym sources k clock (Weak.decides worker htapes result fuel)
    degree copies clauseDegree delta symCap onsetSym
  onsetThr : Nat
  /-- Paper C.10: the same for the threshold class. -/
  encodesThr : EncodesThr sources k clock (Weak.decides worker htapes result fuel)
    degree copies clauseDegree delta thrCap onsetThr
  A : Nat
  B : Nat
  a : Nat
  sigma : Nat
  hot : Nat → Nat
  ha : a ≤ k+1
  hsigma : 6+(fixedProjection sources).degrees.proofLog ≤ sigma
  splitOnset : Nat
  /-- Paper A.7: the polynomial part of the runtime. -/
  hpoly : ∀ N, splitOnset ≤ N → fuel N+2 ≤ A*(N+1)^a+hot N
  /-- Paper A.8: the single residual table factor is damped. -/
  hdamp : ∀ N, splitOnset ≤ N →
    hot N*((outer sources k clock).result.pcp.nativeWidth N)^sigma ≤
      B*2^((outer sources k clock).result.pcp.nativeWidth N)

/-- Every physical witness is a closure at the same fixed gamma. -/
def closureAt_of_physical {sources : EightSources} {gamma : ℝ}
    (w : PhysicalWitness sources gamma) : ClosureAt sources gamma where
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
  fuel := w.fuel
  meaning := Weak.decides w.worker w.htapes w.result w.fuel
  supplier := Weak.allInputRun_of_stepAtInputs w.worker w.htapes w.result w.budget w.fuel w.hfuel w.step
  sound := sound_of_exposes sources w.k w.clock w.constants _ w.exposes
  complSym := completeness_of_encodesSym sources w.k w.clock _ w.degree w.copies w.clauseDegree
    w.delta w.symCap w.onsetSym w.hd w.hh w.encodesSym
  complThr := completeness_of_encodesThr sources w.k w.clock _ w.degree w.copies w.clauseDegree
    w.delta w.thrCap w.onsetThr w.hd w.hh w.encodesThr
  A := w.A
  B := w.B
  a := w.a
  sigma := w.sigma
  hot := w.hot
  ha := w.ha
  hsigma := w.hsigma
  split := ⟨w.splitOnset, fun N hN =>
    ⟨by rw [Weak.runtime_eq]; exact w.hpoly N hN, w.hdamp N hN⟩⟩

/-- The headline theorem from a physical witness at every fixed gamma. -/
theorem theorem25_of_physical
    (physical : (sources : EightSources) → ∀ gamma : ℝ, 0 < gamma → gamma < 1/2 →
      PhysicalWitness sources gamma)
    (sources : EightSources) : OrdinaryHeadlineTheorem25 :=
  theorem25_of_supply
    (fun s gamma hg hh => closureAt_of_physical (physical s gamma hg hh)) sources

end
end NearCubicWires.RepairSource.CloseoutFinal
