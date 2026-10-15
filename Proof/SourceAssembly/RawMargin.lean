import Proof.SourceAssembly.RawActive

namespace NearCubicWires.Admission.Raw
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram SupplierPipeline SupplierEstimator SupplierCapacity
open SupplierListPolynomial SupplierListSchedule SupplierWalkBridge SupplierTouching
open RepairOrdinary.CloseoutRowsRawLogShape
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- `Layout.widthFromTouch` at the constructed width: the raw row width already
contains the packet exponent `degree*ell` as one of its summands, with room to
spare, so `alphabet^degree ≤ 2^(degree*ell) < 2^rowWidth`. -/
theorem degree_lt_rowWidth (z t W h ell : ℕ) :
    z*(2*t*W)*ell < rowWidth z t W h ell ell := by
  have h1 : z*(2*t*W)*ell = 2*z*t*W*ell := by ring
  have h2 : rowWidth z t W h ell ell =
      z*(ell+coordinateLog t W h ell)+2*z*t*W*ell+6 := rfl
  omega

theorem coordinateDegree_lt_rowWidth {q : ℕ} (gs : List (SupportedNormalizedGate q))
    (I : Finset (Fin q)) (den z ell : ℕ) :
    z*(canonicalWalkLength den * structuralListCoordinateRawDegree
        (canonicalGradedDepth (touchingCost (occurrenceSupport gs) I))
        (executableGradedWindow (touchingCost (occurrenceSupport gs) I))
        gradedTerminalWindow)*ell <
      rowWidth z (canonicalWalkLength den) (windowSumAt gs I) (rowDepthAt gs I) ell ell := by
  rw [coordinateDegree_at_eq gs I den]
  exact degree_lt_rowWidth z (canonicalWalkLength den) (windowSumAt gs I) (rowDepthAt gs I) ell

theorem admitted_margin (u v cz ct ce kappa : ℕ) :
    ∃ onset : ℕ, ∀ q, onset ≤ q →
      ∀ (gs : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (z t ell K : ℕ),
      gs.length ≤ 4*q^3 →
      (touchingCost (occurrenceSupport gs) I : ℝ)*(logScale q : ℝ)^(2*(u+v)+4) ≤
        4*kappa*paperCap (shapeCoefficient cz ct ce kappa) kappa*(q : ℝ)^2 →
      z+1 ≤ (cz+1)*(logScale q)^u →
      t+1 ≤ (ct+1)*(logScale q)^v →
      ell+1 ≤ (ce+1)*logScale q →
      K ≤ kappa*logScale q →
      200*(K+rowWidth z t (windowSumAt gs I) (rowDepthAt gs I) ell ell*(K+2)) ≤ q-K ∧
        67 ≤ q-K := by
  obtain ⟨onset,hmargin⟩ := paper_margin_eventual (shapeCoefficient cz ct ce kappa) kappa (u+v)
  refine ⟨onset,?_⟩
  intro q hq gs I z t ell K hpop hactive hz ht he hK
  have hlog : 1 ≤ logScale q := logScale_pos q
  have hW := window_depth_shape_at gs I hpop
  have hcost := load_shape z t (windowSumAt gs I) (rowDepthAt gs I) ell ell K (logScale q)
    cz ct ce kappa u v (Real.sqrt (touchingCost (occurrenceSupport gs) I))
    (Real.sqrt_nonneg _) hlog le_rfl hz ht he hK hW
  exact hmargin q hq (touchingCost (occurrenceSupport gs) I) K
    (K+rowWidth z t (windowSumAt gs I) (rowDepthAt gs I) ell ell*(K+2)) hK hactive hcost

end
end NearCubicWires.Admission.Raw
