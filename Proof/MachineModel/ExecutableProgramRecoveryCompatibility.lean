import Proof.Foundations.ExecutableProgramTightRefuterSource
import Proof.Foundations.OuterPCPRecovery

namespace NearCubicWires.ExecutableProgramRecoveryCompatibility

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableProgramTimedSource
open NearCubicWires.ExecutableProgramTightRefuterSource
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.RecoveryPipeline
open NearCubicWires.SourceInterfaces

/-- The legacy refuter witness is a semantic view of the fixed executable
hierarchy program, not an independently selected language. -/
def ExecutableProgramRefuterSource.toFixedRefuterWitness
    {bound : ℕ → ℕ} (source : ExecutableProgramRefuterSource bound) :
    FixedRefuterWitness source.hierarchyProgram.language bound where
  refuter := source.refuter
  sound := source.sound

/-- Fill the existing outer-PCP record from one program-indexed result. -/
def toLegacyHierarchyOuterPCP
    {bound : ℕ → ℕ} (source : ExecutableProgramRefuterSource bound)
    {runnerDegree queryExponent substitutionExponent : ℕ}
    (result : ExecutableProgramProjectionPCPResult source.hierarchyProgram
      bound runnerDegree queryExponent substitutionExponent) :
    HierarchyOuterPCP source.toLegacy where
  runnerDegree := runnerDegree
  queryExponent := queryExponent
  substitutionExponent := substitutionExponent
  pcp := result.pcp
  proofExponent := result.proofExponent
  substitution := result.substitution
  shapeDegree := result.shapeDegree
  queryDegree := result.queryDegree
  decisionDegree := result.decisionDegree
  substitutionDegree := result.substitutionDegree
  queryCountBound := result.queryCountBound
  compactQueryCountBound := result.compactQueryCountBound
  decisionLengthBound := result.decisionLengthBound
  proofSizeBound := result.proofSizeBound
  substitutionSizeBound := result.substitutionSizeBound
  complete := result.complete
  sound := result.sound

/-- Corrected replacement for the old recovery join.  The returned object is
the existing recovery type, but the uniform source was applied only to the
fixed executable hierarchy program. -/
theorem existsLegacyHierarchyOuterPCP
    {bound : ℕ → ℕ} (admissible : RefuterClockAdmissible bound)
    (source : ExecutableProgramRefuterSource bound)
    (projection : UniformExecutableProgramProjectionPCPSource) :
    Nonempty
      { outer : HierarchyOuterPCP source.toLegacy //
        outer.runnerDegree = projection.runnerDegree ∧
          outer.queryExponent = projection.queryExponent ∧
          outer.substitutionExponent = projection.substitutionExponent } := by
  rcases hierarchyProjectionPCP admissible source projection with ⟨result⟩
  exact ⟨⟨toLegacyHierarchyOuterPCP source result, rfl, rfl, rfl⟩⟩

/-- Tight sources feed the same recovery surface only through the faithful
program-backed intermediate projection. -/
theorem existsLegacyHierarchyOuterPCP_of_tightSource
    {bound : ℕ → ℕ} (admissible : RefuterClockAdmissible bound)
    (source : CertifiedTightExecutableProgramRefuterSource bound)
    (projection : UniformExecutableProgramProjectionPCPSource) :
    Nonempty
      (HierarchyOuterPCP source.toLegacy) := by
  rcases existsLegacyHierarchyOuterPCP admissible source.toProgramSource
      projection with ⟨outer⟩
  exact ⟨outer.1⟩

end NearCubicWires.ExecutableProgramRecoveryCompatibility
