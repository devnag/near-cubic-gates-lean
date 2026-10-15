import Proof.CaseAnalysis.FinalParameters

/-! **Supersedes `exists_closureParameters`.**

Paper freeze order (paper.tex:474) puts the *validity tolerance* before the
*supplier accuracy*, so `constants` is fixed before `delta`. The earlier lemma
ignored that and chose `delta := 1/4`, which is unusable: paper C.10 runs its
completeness through `honest_estimates_pass`, whose hypothesis is
`honestError ≤ zeta constants`, while `EncodesSym`/`EncodesThr` supply only
`honestError ≤ delta`. Since `zeta constants = (gap constants)^2/1000000` and
`gap < 1`, we have `zeta < 10^-6`, so `delta = 1/4` cannot discharge it.

Taking `delta := zeta constants` closes the gap by equality and costs nothing:
`constant_copies` accepts any rational in `(0, 1/2]` and merely returns a larger
constant XOR power, which the paper explicitly allows -- "the XOR power is a
fixed constant, enlarged once to dominate the Case-1 amplifier arity". -/
namespace NearCubicWires.RepairSource.CloseoutFinal
open SourceInterfaces RepairRepresentation CloseoutLanguage CloseoutParameters
open CompetitorRationalGap
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- Every parameter field of `PhysicalWitness`, at one fixed gamma, with the
validity tolerance already fixed. `delta = zeta constants` is what the
completeness chain needs. -/
theorem exists_closureParametersZeta (sources : EightSources)
    (constants : Constants (selectedPCPP sources)) (gamma : ℝ) (hg : 0 < gamma) :
    ∃ (degree copies clauseDegree : Nat),
      17*sources.amplification.stvExponent ≤ degree ∧
      (selectedAmplifier sources.amplification degree).arityCoefficient ≤ copies ∧
      1 ≤ clauseDegree ∧ ClauseReady sources degree clauseDegree ∧
      0 < zeta constants ∧ zeta constants < 1/2 ∧
      xorEpsilon ((zeta constants : ℚ) : ℝ) copies < gamma := by
  have hpos : 0 < zeta constants := zeta_positive constants
  have hhalfR : ((zeta constants : ℚ) : ℝ) < 1/2 := radius_lt_half constants
  have hhalf : zeta constants < 1/2 := by
    have h : ((zeta constants : ℚ) : ℝ) < ((1/2 : ℚ) : ℝ) := by push_cast; exact hhalfR
    exact_mod_cast h
  obtain ⟨copies, _hpos, hcover, heps⟩ :=
    constant_copies (zeta constants) hpos (le_of_lt hhalfR) gamma hg
      (selectedAmplifier sources.amplification (17*sources.amplification.stvExponent)).arityCoefficient
  obtain ⟨clauseDegree, hD, hready⟩ :=
    exists_clauseReady sources (17*sources.amplification.stvExponent)
  exact ⟨17*sources.amplification.stvExponent, copies, clauseDegree,
    Nat.le_refl _, hcover, hD, hready, hpos, hhalf, heps⟩

end NearCubicWires.RepairSource.CloseoutFinal
