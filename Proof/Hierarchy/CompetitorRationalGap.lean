import Proof.Foundations.RepresentationSourceContracts

/-! Local rational constants for the same pointwise PCPP witness. Narrowing
the open real gap changes neither output instances nor either actual source
program. These fixed rational choices precede the weak machine and its input.
The physical comparator can therefore use exact finite scalar words. -/
namespace NearCubicWires.RepairSource.CompetitorRationalGap
open RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Constants (source : PointwisePCPPAlgorithm) where
  soundness : ℚ
  completeness : ℚ
  lower : source.soundness<(soundness : ℝ)
  separation : soundness<completeness
  upper : (completeness : ℝ)<source.completeness

theorem constants_exist (source : PointwisePCPPAlgorithm) : Nonempty (Constants source) := by
  obtain ⟨s,hs,hsc⟩ := exists_rat_btwn source.gap
  obtain ⟨c,hc,hcc⟩ := exists_rat_btwn hsc
  refine ⟨⟨s,c,hs,?_,hcc⟩⟩
  exact_mod_cast hc

def narrowed (source : PointwisePCPPAlgorithm) (constants : Constants source) : PointwisePCPPAlgorithm :=
  {source with
    soundness := constants.soundness
    completeness := constants.completeness
    soundnessPositive := source.soundnessPositive.trans constants.lower
    gap := by exact_mod_cast constants.separation
    completenessBelowOne := constants.upper.trans source.completenessBelowOne
    complete := fun r x hx => constants.upper.le.trans (source.complete r x hx)
    sound := fun r x hx aux => (source.sound r x hx aux).trans constants.lower.le}

theorem same_output (source : PointwisePCPPAlgorithm) (constants : Constants source) :
    (narrowed source constants).output=source.output := rfl

theorem same_constructor (source : PointwisePCPPAlgorithm) (constants : Constants source) :
    (narrowed source constants).constructor=source.constructor := rfl

theorem same_honest (source : PointwisePCPPAlgorithm) (constants : Constants source) :
    (narrowed source constants).honest=source.honest := rfl

def gap {source : PointwisePCPPAlgorithm} (constants : Constants source) : ℚ :=
  constants.completeness-constants.soundness
def midpoint {source : PointwisePCPPAlgorithm} (constants : Constants source) : ℚ :=
  (constants.completeness+constants.soundness)/2
def estimationTolerance {source : PointwisePCPPAlgorithm} (constants : Constants source) (zeta : ℚ) : ℚ :=
  min zeta (gap constants/20)

theorem tolerance_positive {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (zeta : ℚ) (hz : 0<zeta) : 0<estimationTolerance constants zeta := by
  simp only [estimationTolerance,lt_min_iff]
  exact ⟨hz,div_pos (sub_pos.mpr constants.separation) (by norm_num)⟩

theorem midpoint_sound {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (estimate error : ℝ)
    (herr : error≤(gap constants : ℝ)/20)
    (hestimate : estimate≤(constants.soundness : ℝ)+error+(gap constants : ℝ)/10) :
    estimate<(midpoint constants : ℝ) := by
  have hg : (constants.soundness : ℝ)<constants.completeness := by exact_mod_cast constants.separation
  simp only [gap,Rat.cast_sub,midpoint,Rat.cast_div,Rat.cast_add,Rat.cast_ofNat] at *
  linarith

theorem midpoint_complete {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (estimate error : ℝ)
    (herr : error≤(gap constants : ℝ)/20)
    (hestimate : (constants.completeness : ℝ)-error-(gap constants : ℝ)/10≤estimate) :
    (midpoint constants : ℝ)<estimate := by
  have hg : (constants.soundness : ℝ)<constants.completeness := by exact_mod_cast constants.separation
  simp only [gap,Rat.cast_sub,midpoint,Rat.cast_div,Rat.cast_add,Rat.cast_ofNat] at *
  linarith

end NearCubicWires.RepairSource.CompetitorRationalGap
