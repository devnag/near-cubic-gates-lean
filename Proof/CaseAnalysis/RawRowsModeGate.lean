import Proof.CaseAnalysis.RawRowsThresholdSize
import Proof.CaseAnalysis.RawRowsModeBounds

/-! One source-fixed logarithmic width feeds the actual raw printer load.
This is the common final resource consumer for SYM5 and THR9. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open SupplierPipeline SupplierEstimator SupplierWalkBridge SupplierTouching
open SourceInterfaces RepairRepresentation PolynomialSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem actual_log_bounds (a : DecompositionAlgorithm) (degree : ℕ) :
    ∃ ce : ℕ, 0 < ce ∧ ∀ q (gs : List (SupportedNormalizedGate q)),
      gs.length ≤ 4*q^3 →
      (∀ i,(gs.get i).descriptionBits ≤ descriptionEnvelope degree q) →
      natBitLength (2*gs.length+1) ≤ ce*logScale q ∧
      ∀ i,(occurrenceExactChildren a gs i).length ≤ 2^(ce*logScale q) := by
  obtain ⟨ci,hci,hi⟩ := actual_children_log a degree
  obtain ⟨cp,hcp,hp⟩ := population_bits_log
  refine ⟨ci+cp,by omega,?_⟩
  intro q gs hpop hd
  constructor
  · have h := hp q gs.length hpop
    have hm := Nat.mul_le_mul_right (logScale q) (Nat.le_add_left cp ci)
    omega
  · intro i
    exact (hi q gs hd i).le.trans
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.le_add_right ci cp)))

def modeLoad {q : ℕ} (gs : List (SupportedNormalizedGate q)) (kappa den z ce : ℕ) :=
  let K := normalizedLiveCount q kappa
  K+actualWidth gs kappa den z (ce*logScale q) (ce*logScale q)*(K+2)

theorem mode_load_shape {q : ℕ} (gs : List (SupportedNormalizedGate q))
    (kappa den z ce cz ct u v : ℕ) (hpop : gs.length ≤ 4*q^3)
    (hz : z+1 ≤ (cz+1)*logScale q^u)
    (ht : canonicalWalkLength den+1 ≤ (ct+1)*logScale q^v) :
    (modeLoad gs kappa den z ce : ℝ) ≤
      (shapeCoefficient cz ct ce kappa : ℝ)*
        (Real.sqrt (touchingCost (occurrenceSupport gs) (normalizedLiveSet gs kappa))+
          (logScale q : ℝ))*(logScale q : ℝ)^(u+v+2) := by
  have he : ce*logScale q+1 ≤ (ce+1)*logScale q := by
    have h := logScale_pos q
    nlinarith
  exact load_shape z (canonicalWalkLength den) (windowSum gs kappa) (rowDepth gs kappa)
    (ce*logScale q) (ce*logScale q) (normalizedLiveCount q kappa) (logScale q)
    cz ct ce kappa u v _ (Real.sqrt_nonneg _) (logScale_pos q) le_rfl hz ht he
    (Nat.min_le_right _ _) (window_depth_shape gs kappa hpop)

theorem mode_paper_gate (kappa ce cz ct u v : ℕ) :
    ∃ onset, ∀ q, onset ≤ q → ∀ (gs : List (SupportedNormalizedGate q)) den z,
      gs.length ≤ 4*q^3 →
      z+1 ≤ (cz+1)*logScale q^u →
      canonicalWalkLength den+1 ≤ (ct+1)*logScale q^v →
      (touchingCost (occurrenceSupport gs) (normalizedLiveSet gs kappa) : ℝ)*
        (logScale q : ℝ)^(2*(u+v)+4) ≤
          4*kappa*paperCap (shapeCoefficient cz ct ce kappa) kappa*(q : ℝ)^2 →
      200*modeLoad gs kappa den z ce ≤ q-normalizedLiveCount q kappa ∧
        67 ≤ q-normalizedLiveCount q kappa := by
  obtain ⟨onset,hm⟩ := paper_margin_eventual (shapeCoefficient cz ct ce kappa) kappa (u+v)
  refine ⟨onset,?_⟩
  intro q hq gs den z hpop hz ht hactive
  exact hm q hq _ _ _ (Nat.min_le_right _ _) hactive
    (mode_load_shape gs kappa den z ce cz ct u v hpop hz ht)

end
end NearCubicWires.RepairSource.CloseoutRawRows
