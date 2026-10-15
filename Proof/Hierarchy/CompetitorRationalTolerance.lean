import Proof.Hierarchy.CompetitorRationalGap

/-! One explicit rational choice pays both the componentwise validity and
acceptance midpoint budgets after the pointwise PCPP has been frozen. -/
namespace NearCubicWires.RepairSource.CompetitorRationalGap
open RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def zeta {source : PointwisePCPPAlgorithm} (constants : Constants source) : ℚ :=
  (gap constants)^2/1000000
def meanThreshold {source : PointwisePCPPAlgorithm} (constants : Constants source) : ℚ :=
  2*zeta constants
def momentThreshold {source : PointwisePCPPAlgorithm} (constants : Constants source) : ℚ :=
  1+zeta constants

theorem zeta_positive {source : PointwisePCPPAlgorithm} (constants : Constants source) :
    0<zeta constants := by
  have hg : 0<gap constants := sub_pos.mpr constants.separation
  exact div_pos (sq_pos_of_pos hg) (by norm_num)

theorem validity_rounding_slack {source : PointwisePCPPAlgorithm} (constants : Constants source) :
    6*Real.sqrt (12*(zeta constants : ℝ))<(gap constants : ℝ)/10 := by
  have hg : 0<(gap constants : ℝ) := by exact_mod_cast sub_pos.mpr constants.separation
  have hz : 0<(zeta constants : ℝ) := by exact_mod_cast zeta_positive constants
  have hs := Real.sq_sqrt (show 0≤12*(zeta constants : ℝ) by positivity)
  have hnon := Real.sqrt_nonneg (12*(zeta constants : ℝ))
  have he : (zeta constants : ℝ)=(gap constants : ℝ)^2/1000000 := by
    simp [zeta]
  rw [he] at hs hnon ⊢
  nlinarith

theorem full_error_budget {source : PointwisePCPPAlgorithm} (constants : Constants source) :
    0<estimationTolerance constants (zeta constants) ∧
    estimationTolerance constants (zeta constants)≤zeta constants ∧
    estimationTolerance constants (zeta constants)≤gap constants/20 ∧
    6*Real.sqrt (12*(zeta constants : ℝ))<(gap constants : ℝ)/10 := by
  exact ⟨tolerance_positive constants _ (zeta_positive constants),min_le_left _ _,
    min_le_right _ _,validity_rounding_slack constants⟩

theorem no_branch_below_midpoint {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (estimate : ℝ)
    (hestimate : estimate≤(constants.soundness : ℝ)+
      estimationTolerance constants (zeta constants)+6*Real.sqrt (12*(zeta constants : ℝ))) :
    estimate<(midpoint constants : ℝ) := by
  apply midpoint_sound constants estimate (estimationTolerance constants (zeta constants))
  · exact_mod_cast (full_error_budget constants).2.2.1
  · have hs := validity_rounding_slack constants
    linarith

theorem yes_branch_above_midpoint {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (estimate : ℝ)
    (hestimate : (constants.completeness : ℝ)-
      estimationTolerance constants (zeta constants)-6*Real.sqrt (12*(zeta constants : ℝ))≤estimate) :
    (midpoint constants : ℝ)<estimate := by
  apply midpoint_complete constants estimate (estimationTolerance constants (zeta constants))
  · exact_mod_cast (full_error_budget constants).2.2.1
  · have hs := validity_rounding_slack constants
    linarith

end NearCubicWires.RepairSource.CompetitorRationalGap
