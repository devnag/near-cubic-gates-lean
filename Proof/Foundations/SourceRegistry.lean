import Proof.Foundations.HierarchySourceContract
import Proof.Foundations.ProjectionSourceContract
import Proof.Foundations.RepresentationSourceContracts

/-! The repaired eight source groups, containing ten literature constituents.
No U, ordinary simulator, rational bound, codec or local running-time supplier
is an imported field. The final target records ordinary E^NP explicitly. -/
namespace NearCubicWires.RepairSource
open SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure PCPSourceGroup : Prop where
  projection : ProjectionPCPSource
  proximity : PointwisePCPPSource

structure RefuterXorSourceGroup : Prop where
  hierarchyRefuter : HierarchyRefuterSource
  xor : XorSource

structure EightSources : Prop where
  normalization : ThresholdNormalizationContract
  decomposition : DecompositionSource
  williams : WilliamsSource
  expander : ExpanderSpectrumContract
  prime : PrimeThetaBoundContract
  pcp : PCPSourceGroup
  refuterXor : RefuterXorSourceGroup
  amplifier : Nonempty SourceAmplifierFactory

/-- Literal paper Theorem2.5, with ordinary E^NP membership. The source repair
changes no circuit class, common-language quantifier, strictness or exponent.
This is the target proposition, not a claim that it has been proved. -/
noncomputable def OrdinaryHeadlineTheorem25 : Prop :=
  ∀ fixedAdvantage : ℝ,
    0 < fixedAdvantage → fixedAdvantage < 1 / 2 →
    ∃ language : Language,
    ∃ symmetricCoefficient thresholdCoefficient : ℝ,
      OrdinaryInENP language ∧
      0 < symmetricCoefficient ∧
      0 < thresholdCoefficient ∧
      ∃ onset : ℕ, ∀ n : ℕ, onset ≤ n →
        (∀ circuit : SymmetricThresholdCircuit n,
          1 / 2 + fixedAdvantage ≤ agreement circuit.eval (language n) →
          wireScale symmetricCoefficient 5 n < circuit.wireCount) ∧
        (∀ circuit : ThresholdThresholdCircuit n,
          1 / 2 + fixedAdvantage ≤ agreement circuit.eval (language n) →
          wireScale thresholdCoefficient 9 n < circuit.wireCount)

noncomputable def EightSources.hierarchy (sources : EightSources)
    (T : ℕ → ℕ) (clock : OrdinaryClock T) : HierarchyRefuterAlgorithm T :=
  Classical.choice (sources.refuterXor.hierarchyRefuter T clock)

noncomputable def EightSources.amplification (sources : EightSources) :
    SourceAmplifierFactory := Classical.choice sources.amplifier

/-- The registry supplies exactly the corrected source witnesses at the
enclosing recovery consumer. Its PCP and competitor are LOCAL realizations. -/
theorem registered_scheduled_recovery (sources : EightSources)
    (T : ℕ → ℕ) (clock : OrdinaryClock T) (degrees : PCPDegrees)
    (outer : ChangedHierarchyOuterPCP (sources.hierarchy T clock).joint degrees)
    (M : OrdinaryWeakMachine) (littleO : OrdinaryLittleO M T)
    (oneSided : ∀ n x, M.accepts n x →
      (sources.hierarchy T clock).hierarchy.timedView.accepts n x = true)
    (d : ℕ) :
    ∃ onset, ∀ n, onset ≤ n → 1 ≤ outer.result.pcp.nativeWidth n →
      Nonempty (ScheduledOuterCase outer.result.pcp
        (selectedAmplifier sources.amplification d).toScheduleAmplifier
        ((sources.hierarchy T clock).output M n)) :=
  hierarchy_source_scheduled_recovery (sources.hierarchy T clock) degrees
    outer M littleO oneSided sources.amplification d

end NearCubicWires.RepairSource
