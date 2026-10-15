import Proof.Foundations.PolynomialClock
import Proof.Foundations.RecoveryPipeline

/-!
# Closing the fixed-machine/refuter clock quantifiers

The executable refuter contract chooses its timed hierarchy *after* the clock.
Accordingly, the local compiler first proves one structural verifier-degree
bound, then freezes a pairing clock above that bound, and only then constructs
the hierarchy-dependent weak machine.  This is the CLW quantifier order.
-/

namespace NearCubicWires.RefuterClockClosure

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryPipeline
open NearCubicWires.SourceInterfaces

/-- Apply the already-uniform projection-PCP source only to the genuine timed
hierarchy machine returned by the refuter source.  Its three structural
exponents were fixed before this source existed. -/
theorem hierarchyProjectionPCP
    {bound : ℕ → ℕ} (admissible : RefuterClockAdmissible bound)
    (source : ExecutableRefuterSource bound)
    (projection : UniformProjectionPCPSource) :
    ∃ pcp : ExecutableProjectionPCP source.hierarchyMachine bound,
      ∃ proofExponent : ℕ,
        ∃ substitution : ExecutableProjectionSubstitution pcp,
          pcp.shape.degree ≤ projection.runnerDegree ∧
          pcp.query.degree ≤ projection.runnerDegree ∧
          pcp.decisionRunner.degree ≤ projection.runnerDegree ∧
          substitution.runner.degree ≤ projection.runnerDegree ∧
          (∀ n, pcp.queryCount n ≤ pcp.shape.budget n) ∧
          (∀ n,
            pcp.queryCount n ≤
              pcp.shape.coefficient *
                (pcp.nativeWidth n + 1) ^ projection.queryExponent) ∧
          (∀ n input randomness,
            (pcp.decision (n := n) input randomness).clauses.length ≤
              pcp.decisionRunner.budget
                (pcp.decisionRequest input randomness)) ∧
          (∀ n,
            2 ^ pcp.nativeWidth n ≤
              pcp.shape.coefficient * bound n *
                logScale (bound n) ^ proofExponent) ∧
          (∀ request,
            (substitution.circuit request).size ≤
              substitution.sizeCoefficient *
                (pcp.nativeWidth request.inputArity +
                  request.oracle.size + 1) ^
                    projection.substitutionExponent) ∧
          (∀ n input, source.hierarchyMachine.accepts n input →
            ∃ proof, ∀ randomness,
              pcp.toSemantic.accepts input proof randomness) ∧
          (∀ n input, ¬source.hierarchyMachine.accepts n input →
            ∀ proof, pcp.toSemantic.acceptanceFraction input proof ≤
              1 / ((n + 1 : ℕ) : ℝ) ^ 10) :=
  projection.guarantee source.hierarchyMachine bound
    source.hierarchySteps admissible.atLeastInput

/-- Instantiate the fixed refuter at a preselected structural degree bound.
The same bound is the clock depth; `depth < 2 ^ depth` supplies the strict
runtime inequality even at zero.  Allowing the clock to depend on the returned
hierarchy machine would reverse the imported quantifiers. -/
theorem existsFixedRefuterForMachine
    (contract : ExecutableRefuterContract)
    (depth : ℕ)
    (machineFor :
      ExecutableRefuterSource (pairClock depth) →
        ExecutableWeakNondeterministicMachine)
    (verifierDegreeBound :
      ∀ source, (machineFor source).verifier.degree ≤ 2 ^ depth)
    (verifierSavingBound :
      ∀ source, 1 ≤ (machineFor source).verifier.logPower)
    (witnessBound :
      ∀ source n, (machineFor source).witnessBits n ≤ n / 10) :
    ∃ source : ExecutableRefuterSource (pairClock depth),
      let machine := machineFor source
      Nonempty
          (FixedRefuterWitness source.hierarchyMachine.accepts
            (pairClock depth)) ∧
        RunsInLittleO machine.toSemantic (pairClock depth) ∧
        (∀ n, machine.witnessBits n ≤ n / 10) := by
  rcases contract (pairClock depth) (pairClockAdmissible depth) with ⟨source⟩
  let machine := machineFor source
  have hwitness : ∀ n, machine.witnessBits n ≤ n / 10 := by
    intro n
    exact witnessBound source n
  have hwitnessLinear : ∀ n, machine.witnessBits n ≤ n := by
    intro n
    exact (hwitness n).trans (Nat.div_le_self n 10)
  have hruntime :
      RunsInLittleO machine.toSemantic (pairClock depth) :=
    executableMachine_quotient_runsInLittleO_pairClock machine depth
      (verifierDegreeBound source) (verifierSavingBound source)
      hwitnessLinear
  refine ⟨source, ?_⟩
  change
    Nonempty
        (FixedRefuterWitness source.hierarchyMachine.accepts
          (pairClock depth)) ∧
      RunsInLittleO machine.toSemantic (pairClock depth) ∧
      (∀ n, machine.witnessBits n ≤ n / 10)
  exact
    ⟨⟨{ refuter := source.refuter, sound := source.sound }⟩,
      hruntime, hwitness⟩

end NearCubicWires.RefuterClockClosure
