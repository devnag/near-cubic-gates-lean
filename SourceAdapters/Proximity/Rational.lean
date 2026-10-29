import NineInputs
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-!
Q01, `app:sources`, "Uniform three-query PCPP and code interfaces": fix a positive rational proximity parameter strictly below
half of the requested real distance. This module does not encode the parameter
as machine input. The constructor is chosen after the rational is fixed.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": the rational source proximity is fixed after `delta`. -/
theorem exists_rational_proximity {delta : ℝ} (hpos : 0 < delta)
    (hlt : delta < 1) :
    ∃ eta : ℚ, 0 < eta ∧ eta < 1 ∧ (eta : ℝ) < delta / 2 := by
  obtain ⟨eta, hepos, helt⟩ := exists_rat_btwn (show (0 : ℝ) < delta / 2 by linarith)
  refine ⟨eta, by exact_mod_cast hepos, ?_, helt⟩
  have : (eta : ℝ) < 1 := by linarith
  exact_mod_cast this

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": closed target distance gives the source's strict distance.
The statement remains valid when the accepting set is empty. -/
theorem strict_far_of_far {delta : ℝ} {eta : ℚ} (hgap : (eta : ℝ) < delta)
    {C : Circuit} {input : BitInput C.n} (hfar : ProximityFar delta C input) :
    ∀ accepted : BitInput C.n, C.D.eval accepted = true →
      (eta : ℝ) < relativeHamming input accepted := by
  intro accepted haccepted
  exact hgap.trans_le (hfar accepted haccepted)

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": one rational choice works for every circuit and input. -/
theorem rational_proximity_for_all_circuits {delta : ℝ} (hpos : 0 < delta)
    (hlt : delta < 1) :
    ∃ eta : ℚ, 0 < eta ∧ eta < 1 ∧ (eta : ℝ) < delta / 2 ∧
      ∀ (C : Circuit) (input : BitInput C.n), ProximityFar delta C input →
        ∀ accepted : BitInput C.n, C.D.eval accepted = true →
          (eta : ℝ) < relativeHamming input accepted := by
  obtain ⟨eta, hepos, helt, hedelta⟩ := exists_rational_proximity hpos hlt
  refine ⟨eta, hepos, helt, hedelta, ?_⟩
  intro C input hfar
  exact strict_far_of_far (by linarith) hfar

end NearCubicGates.Adapters.Proximity
