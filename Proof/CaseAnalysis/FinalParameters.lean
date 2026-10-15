import Proof.CaseAnalysis.FinalAssembly
import Proof.CaseAnalysis.Parameters

/-! Paper `thm:main-fixed` parameter order, discharged once and for all.

gamma is fixed first. Then the STV exponent fixes `degree`; the selected
amplifier's arity coefficient and `constant_copies` fix one constant `copies`;
`exists_clauseReady` fixes `clauseDegree`. `delta` is any fixed rational in
`(0, 1/2)` -- the paper fixes it, it is never input-dependent -- and `1/4`
serves. Nothing here depends on the length `N`, on the input, or on the
machine, which is exactly the paper's requirement. -/
namespace NearCubicWires.RepairSource.CloseoutFinal
open SourceInterfaces RepairRepresentation CloseoutLanguage CloseoutParameters
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- Every parameter field of `PhysicalWitness`, at one fixed gamma. -/
theorem exists_closureParameters (sources : EightSources) (gamma : ℝ) (hg : 0 < gamma) :
    ∃ (degree copies clauseDegree : Nat) (delta : ℚ),
      17*sources.amplification.stvExponent ≤ degree ∧
      (selectedAmplifier sources.amplification degree).arityCoefficient ≤ copies ∧
      1 ≤ clauseDegree ∧ ClauseReady sources degree clauseDegree ∧
      0 < delta ∧ delta < 1/2 ∧ xorEpsilon (delta : ℝ) copies < gamma := by
  refine ⟨17*sources.amplification.stvExponent, ?_⟩
  obtain ⟨copies, _hpos, hcover, heps⟩ :=
    constant_copies (1/4 : ℚ) (by norm_num) (by norm_num) gamma hg
      (selectedAmplifier sources.amplification (17*sources.amplification.stvExponent)).arityCoefficient
  obtain ⟨clauseDegree, hD, hready⟩ :=
    exists_clauseReady sources (17*sources.amplification.stvExponent)
  exact ⟨copies, clauseDegree, 1/4, Nat.le_refl _, hcover, hD, hready,
    by norm_num, by norm_num, heps⟩

end NearCubicWires.RepairSource.CloseoutFinal
