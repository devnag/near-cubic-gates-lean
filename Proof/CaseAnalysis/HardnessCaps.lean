import Proof.CaseAnalysis.CaseTwoDirect
import Proof.Foundations.WireScaleTransfer

/-! The actual native-width caps feed BOTH headline circuit classes.
Reuse the existing constant-factor wireScale theorem; only min-one clipping
and same-sampled-sum size transport are required by the final binding. -/
namespace NearCubicWires.RepairSource.CloseoutLanguage
open SourceInterfaces RepairRepresentation CircuitRestriction
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def headlineCoefficient (cap : ℝ) (factor : Nat) : ℝ := min 1 (cap/(factor : ℝ)^3)

theorem headlineCoefficient_positive (cap : ℝ) (factor : Nat)
    (hc : 0 < cap) (hf : 0 < factor) : 0 < headlineCoefficient cap factor:=by
  unfold headlineCoefficient
  apply lt_min (by norm_num)
  exact div_pos hc (pow_pos (by exact_mod_cast hf) _)

theorem headlineCoefficient_le_one (cap : ℝ) (factor : Nat) :
    headlineCoefficient cap factor ≤ 1:=min_le_left _ _

theorem headline_cap_transfer (cap : ℝ) (factor exponent q n : Nat)
    (hc : 0 ≤ cap) (hf : 0 < factor) (hqn : q ≤ n) (hnq : n ≤ factor*q) :
    ⌊wireScale (headlineCoefficient cap factor) exponent n⌋₊ ≤ 
      ⌊wireScale cap exponent q⌋₊:=by
  apply Nat.floor_mono
  exact (wireScale_mono_coefficient (min_le_right _ _) exponent n).trans
    (WireScaleTransfer.wireScale_shrink_cube hc factor exponent hf hqn hnq)

def sampled_weaken {family : SizedFunctionFamily} {delta : ℚ}
    {n copies size size' : Nat} {f : BoolFunction n}
    (h : ∀ g,family n g size → family n g size')
    (w : SampledXorSum family delta n copies size f) :
    SampledXorSum family delta n copies size' f where
  sum := ⟨w.sum.terms,fun term ht=>h term.2 (w.sum.legal term ht),w.sum.inUnitInterval⟩
  form := w.form
  close := w.close

def symmetric_sampled_weaken {delta : ℚ} {n copies size size' : Nat} {f : BoolFunction n}
    (h : size ≤ size') (w : SampledXorSum symmetricWireFamily delta n copies size f) :
    SampledXorSum symmetricWireFamily delta n copies size' f :=
  sampled_weaken (fun _ ⟨c,hc,he⟩=>⟨c,hc.trans h,he⟩) w

def threshold_sampled_weaken {delta : ℚ} {n copies size size' : Nat} {f : BoolFunction n}
    (h : size ≤ size') (w : SampledXorSum thresholdWireFamily delta n copies size f) :
    SampledXorSum thresholdWireFamily delta n copies size' f :=
  sampled_weaken (fun _ ⟨c,hc,he⟩=>⟨c,hc.trans h,he⟩) w

end
end NearCubicWires.RepairSource.CloseoutLanguage
