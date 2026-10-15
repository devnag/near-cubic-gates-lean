import Proof.SourceAssembly.RawMargin

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

theorem one_le_rowWidth (z t W h ell : ℕ) : 1 ≤ rowWidth z t W h ell ell := by
  have h2 : rowWidth z t W h ell ell =
      z*(ell+coordinateLog t W h ell)+2*z*t*W*ell+6 := rfl
  omega

/-- SYM's `v = 0` is a THEOREM, not an assumption.  `symmetricListDenominator
r target = r.circuits.length*(target+1)` and the stage target is a constant
function of the arity (`stageTarget = fun _ => accuracyTargetAll …`), so the
canonical walk length has a bound independent of `q`. -/
theorem symmetric_walk_constant (target : ℕ)
    (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (hfour : r.circuits.length ≤ 4) :
    canonicalWalkLength (symmetricListDenominator r target)+1 ≤
      canonicalWalkLength (4*(target+1))+1 := by
  have hm : symmetricListDenominator r target ≤ 4*(target+1) := by
    unfold symmetricListDenominator
    exact Nat.mul_le_mul_right (target+1) hfour
  have hc := Nat.clog_mono_right 2 (Nat.add_le_add_right hm 1)
  unfold canonicalWalkLength
  omega

theorem admitted_layout_sym (ct ce kappa copies : ℕ) (hcopies : 0 < copies) :
    ∃ den0 onset : ℕ, ∀ den : ℕ, den0 ≤ den → ∀ (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
      (I : Finset (Fin r.q)) (rden ell K : ℕ),
      onset ≤ r.q →
      r.circuits.length ≤ 4 →
      canonicalWalkLength rden+1 ≤ ct+1 →
      ell+1 ≤ (ce+1)*logScale r.q →
      K ≤ kappa*logScale r.q →
      r.q * touchingCost (occurrenceSupport (symmetricFourfoldOccurrences r)) I ≤
        normalizedLiveCount r.q kappa *
          supportIncidenceMass (occurrenceSupport (symmetricFourfoldOccurrences r)) →
      (∀ c∈r.circuits, c.wireCount ≤
        max (r.q*(r.q+1)) (copies*⌊wireScale (1/(den : ℝ)) 5 r.q⌋₊)) →
      1 ≤ rowWidth r.circuits.length (canonicalWalkLength rden)
          (windowSumAt (symmetricFourfoldOccurrences r) I)
          (rowDepthAt (symmetricFourfoldOccurrences r) I) ell ell ∧
        r.circuits.length*(canonicalWalkLength rden*structuralListCoordinateRawDegree
            (canonicalGradedDepth (touchingCost
              (occurrenceSupport (symmetricFourfoldOccurrences r)) I))
            (executableGradedWindow (touchingCost
              (occurrenceSupport (symmetricFourfoldOccurrences r)) I))
            gradedTerminalWindow)*ell <
          rowWidth r.circuits.length (canonicalWalkLength rden)
            (windowSumAt (symmetricFourfoldOccurrences r) I)
            (rowDepthAt (symmetricFourfoldOccurrences r) I) ell ell ∧
        67 ≤ r.q-K ∧
        200*(K+rowWidth r.circuits.length (canonicalWalkLength rden)
            (windowSumAt (symmetricFourfoldOccurrences r) I)
            (rowDepthAt (symmetricFourfoldOccurrences r) I) ell ell*(K+2)) ≤ r.q-K := by
  have hcapden : 0 < capDenominator (shapeCoefficient 4 ct ce kappa) kappa := by
    unfold capDenominator; positivity
  obtain ⟨n₁,h₁⟩ := parity_wire_eventual 5 (capDenominator (shapeCoefficient 4 ct ce kappa) kappa)
    hcapden
  obtain ⟨n₂,h₂⟩ := admitted_margin 0 0 4 ct ce kappa
  refine ⟨copies*capDenominator (shapeCoefficient 4 ct ce kappa) kappa,
    max 1 (max n₁ n₂),?_⟩
  intro den hden r I rden ell K hq hfour ht he hK htouch hw
  have hq1 : 1 ≤ r.q := le_trans (Nat.le_max_left _ _) hq
  have hqn1 : n₁ ≤ r.q := le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right 1 _)) hq
  have hqn2 : n₂ ≤ r.q := le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_right 1 _)) hq
  have hpar : ((r.q*(r.q+1) : ℕ) : ℝ) ≤
      wireScale (paperCap (shapeCoefficient 4 ct ce kappa) kappa) 5 r.q := h₁ r.q hqn1
  have hpop := admitted_population_sym r (shapeCoefficient 4 ct ce kappa) kappa copies
    den hcopies hden hfour hpar hw
  have hactive := admitted_active_sym r I (shapeCoefficient 4 ct ce kappa) kappa copies
    den hcopies hden hq1 hfour hpar htouch hw
  have hz : r.circuits.length+1 ≤ (4+1)*(logScale r.q)^0 := by
    simp only [pow_zero, Nat.mul_one]; omega
  have ht' : canonicalWalkLength rden+1 ≤ (ct+1)*(logScale r.q)^0 := by
    simp only [pow_zero, Nat.mul_one]; omega
  obtain ⟨hload,hres⟩ := h₂ r.q hqn2 (symmetricFourfoldOccurrences r) I r.circuits.length
    (canonicalWalkLength rden) ell K hpop hactive hz ht' he hK
  exact ⟨one_le_rowWidth _ _ _ _ _,
    coordinateDegree_lt_rowWidth (symmetricFourfoldOccurrences r) I rden r.circuits.length ell,
    hres,hload⟩

theorem admitted_layout_thr (cz ct ce kappa copies : ℕ) (hcopies : 0 < copies) :
    ∃ den0 onset : ℕ, ∀ den : ℕ, den0 ≤ den → ∀ (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
      (I : Finset (Fin r.q)) (rden z ell K : ℕ),
      onset ≤ r.q →
      r.circuits.length ≤ 4 →
      z+1 ≤ (cz+1)*logScale r.q →
      canonicalWalkLength rden+1 ≤ (ct+1)*logScale r.q →
      ell+1 ≤ (ce+1)*logScale r.q →
      K ≤ kappa*logScale r.q →
      r.q * touchingCost (occurrenceSupport (thresholdFourfoldOccurrences r)) I ≤
        normalizedLiveCount r.q kappa *
          supportIncidenceMass (occurrenceSupport (thresholdFourfoldOccurrences r)) →
      (∀ c∈r.circuits, c.wireCount ≤
        max (r.q*(r.q+1)) (copies*⌊wireScale (1/(den : ℝ)) 9 r.q⌋₊)) →
      1 ≤ rowWidth z (canonicalWalkLength rden)
          (windowSumAt (thresholdFourfoldOccurrences r) I)
          (rowDepthAt (thresholdFourfoldOccurrences r) I) ell ell ∧
        z*(canonicalWalkLength rden*structuralListCoordinateRawDegree
            (canonicalGradedDepth (touchingCost
              (occurrenceSupport (thresholdFourfoldOccurrences r)) I))
            (executableGradedWindow (touchingCost
              (occurrenceSupport (thresholdFourfoldOccurrences r)) I))
            gradedTerminalWindow)*ell <
          rowWidth z (canonicalWalkLength rden)
            (windowSumAt (thresholdFourfoldOccurrences r) I)
            (rowDepthAt (thresholdFourfoldOccurrences r) I) ell ell ∧
        67 ≤ r.q-K ∧
        200*(K+rowWidth z (canonicalWalkLength rden)
            (windowSumAt (thresholdFourfoldOccurrences r) I)
            (rowDepthAt (thresholdFourfoldOccurrences r) I) ell ell*(K+2)) ≤ r.q-K := by
  have hcapden : 0 < capDenominator (shapeCoefficient cz ct ce kappa) kappa := by
    unfold capDenominator; positivity
  obtain ⟨n₁,h₁⟩ := parity_wire_eventual 9 (capDenominator (shapeCoefficient cz ct ce kappa) kappa)
    hcapden
  obtain ⟨n₂,h₂⟩ := admitted_margin 1 1 cz ct ce kappa
  refine ⟨copies*capDenominator (shapeCoefficient cz ct ce kappa) kappa,
    max 1 (max n₁ n₂),?_⟩
  intro den hden r I rden z ell K hq hfour hz ht he hK htouch hw
  have hq1 : 1 ≤ r.q := le_trans (Nat.le_max_left _ _) hq
  have hqn1 : n₁ ≤ r.q := le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right 1 _)) hq
  have hqn2 : n₂ ≤ r.q := le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_right 1 _)) hq
  have hpar : ((r.q*(r.q+1) : ℕ) : ℝ) ≤
      wireScale (paperCap (shapeCoefficient cz ct ce kappa) kappa) 9 r.q := h₁ r.q hqn1
  have hpop := admitted_population_thr r (shapeCoefficient cz ct ce kappa) kappa copies
    den hcopies hden hfour hpar hw
  have hactive := admitted_active_thr r I (shapeCoefficient cz ct ce kappa) kappa copies
    den hcopies hden hq1 hfour hpar htouch hw
  have hz' : z+1 ≤ (cz+1)*(logScale r.q)^1 := by simpa only [pow_one] using hz
  have ht' : canonicalWalkLength rden+1 ≤ (ct+1)*(logScale r.q)^1 := by
    simpa only [pow_one] using ht
  obtain ⟨hload,hres⟩ := h₂ r.q hqn2 (thresholdFourfoldOccurrences r) I z
    (canonicalWalkLength rden) ell K hpop hactive hz' ht' he hK
  exact ⟨one_le_rowWidth _ _ _ _ _,
    coordinateDegree_lt_rowWidth (thresholdFourfoldOccurrences r) I rden z ell,
    hres,hload⟩

end
end NearCubicWires.Admission.Raw
