import Proof.CaseAnalysis.RawRowsPaperCaps
import Proof.CaseAnalysis.RawRowsModeDegree

namespace NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram SupplierPipeline SupplierEstimator SupplierCapacity
open SupplierListPolynomial SupplierListSchedule SupplierWalkBridge SupplierTouching
open RepairOrdinary.CloseoutRowsRawLogShape
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- `touching_log_cap` with the selector's touching inequality as the premise. -/
theorem touching_log_cap_of_touch {q : ℕ} (gs : List (SupportedNormalizedGate q))
    (I : Finset (Fin q)) (kappa r : ℕ) (a : ℝ) (hq : 0 < q)
    (htouch : q * touchingCost (occurrenceSupport gs) I ≤
      normalizedLiveCount q kappa * supportIncidenceMass (occurrenceSupport gs))
    (hcap : (occurrenceWireCount gs : ℝ)*(logScale q : ℝ)^(2*r+5) ≤ 4*a*(q : ℝ)^3) :
    (touchingCost (occurrenceSupport gs) I : ℝ)*(logScale q : ℝ)^(2*r+4) ≤
      4*kappa*a*(q : ℝ)^2 := by
  have hl : (0 : ℝ) < logScale q := by exact_mod_cast logScale_pos q
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have ht := htouch
  rw [supportIncidenceMass_occurrenceSupport] at ht
  have hK : normalizedLiveCount q kappa ≤ kappa*logScale q := Nat.min_le_right _ _
  have ht' : (q : ℝ)*touchingCost (occurrenceSupport gs) I ≤
      (kappa*(logScale q : ℝ))*occurrenceWireCount gs := by
    exact_mod_cast ht.trans (Nat.mul_le_mul_right _ hK)
  apply le_of_mul_le_mul_left (a := (q : ℝ)*logScale q) ?_ (mul_pos hqR hl)
  calc
    ((q : ℝ)*logScale q)*
        ((touchingCost (occurrenceSupport gs) I : ℝ)*(logScale q : ℝ)^(2*r+4)) =
      ((q : ℝ)*touchingCost (occurrenceSupport gs) I)*(logScale q : ℝ)^(2*r+5) := by
          rw [show 2*r+5=(2*r+4)+1 by omega,pow_succ']; ring
    _ ≤ ((kappa : ℝ)*logScale q)*occurrenceWireCount gs*(logScale q : ℝ)^(2*r+5) :=
      mul_le_mul_of_nonneg_right ht' (by positivity)
    _ = ((kappa : ℝ)*logScale q)*((occurrenceWireCount gs : ℝ)*(logScale q : ℝ)^(2*r+5)) := by ring
    _ ≤ ((kappa : ℝ)*logScale q)*(4*a*(q : ℝ)^3) :=
      mul_le_mul_of_nonneg_left hcap (by positivity)
    _ = ((q : ℝ)*logScale q)*(4*kappa*a*(q : ℝ)^2) := by ring

theorem symmetric_active_cap_of_touch (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (I : Finset (Fin r.q)) (kappa : ℕ) (a : ℝ) (ha : 0 ≤ a) (hq : 0 < r.q)
    (hfour : r.circuits.length ≤ 4)
    (htouch : r.q * touchingCost (occurrenceSupport (symmetricFourfoldOccurrences r)) I ≤
      normalizedLiveCount r.q kappa *
        supportIncidenceMass (occurrenceSupport (symmetricFourfoldOccurrences r)))
    (hcap : ∀ c∈r.circuits,(c.wireCount : ℝ) ≤ wireScale a 5 r.q) :
    (touchingCost (occurrenceSupport (symmetricFourfoldOccurrences r)) I : ℝ)*
        (logScale r.q : ℝ)^4 ≤ 4*kappa*a*(r.q : ℝ)^2 :=
  touching_log_cap_of_touch _ I kappa 0 a hq htouch (symmetric_wire_cap r 5 a ha hfour hcap)

theorem threshold_active_cap_of_touch (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (I : Finset (Fin r.q)) (kappa : ℕ) (a : ℝ) (ha : 0 ≤ a) (hq : 0 < r.q)
    (hfour : r.circuits.length ≤ 4)
    (htouch : r.q * touchingCost (occurrenceSupport (thresholdFourfoldOccurrences r)) I ≤
      normalizedLiveCount r.q kappa *
        supportIncidenceMass (occurrenceSupport (thresholdFourfoldOccurrences r)))
    (hcap : ∀ c∈r.circuits,(c.wireCount : ℝ) ≤ wireScale a 9 r.q) :
    (touchingCost (occurrenceSupport (thresholdFourfoldOccurrences r)) I : ℝ)*
        (logScale r.q : ℝ)^8 ≤ 4*kappa*a*(r.q : ℝ)^2 :=
  touching_log_cap_of_touch _ I kappa 2 a hq htouch (threshold_wire_cap r 9 a ha hfour hcap)

/-- Depth and window sum at an arbitrary live set; with `I := CyclicChoice.live occ L`
these are the quantities inside the accepted `Packets.coordinateDegree`. -/
def rowDepthAt {q : ℕ} (gs : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) : ℕ :=
  canonicalGradedDepth (touchingCost (occurrenceSupport gs) I)
def windowSumAt {q : ℕ} (gs : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) : ℕ :=
  ∑ i : Fin (rowDepthAt gs I), executableGradedWindow (touchingCost (occurrenceSupport gs) I) i

theorem window_sum_real_at {q : ℕ} (gs : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) :
    (windowSumAt gs I : ℝ) ≤ 384*Real.sqrt
      (touchingCost (occurrenceSupport gs) I)+65*(rowDepthAt gs I) := by
  have h := sum_gradedWindow_cast_le (touchingCost (occurrenceSupport gs) I) (rowDepthAt gs I)
  unfold windowSumAt
  push_cast
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [executableGradedWindow_eq_gradedWindow]

/-- `window_depth_shape` at an arbitrary live set. -/
theorem window_depth_shape_at {q : ℕ} (gs : List (SupportedNormalizedGate q)) (I : Finset (Fin q))
    (hpop : gs.length ≤ 4*q^3) :
    ((windowSumAt gs I+rowDepthAt gs I+1 : ℕ) : ℝ) ≤
      1400*(Real.sqrt (touchingCost (occurrenceSupport gs) I)+(logScale q : ℝ)) := by
  have hw := window_sum_real_at gs I
  have hd := canonicalGradedDepth_le_logScale_of_activeBound q _
    ((touchingCost_le_occurrenceLength gs I).trans hpop)
  change rowDepthAt gs I ≤ 10*(logScale q+1) at hd
  have hl : (1 : ℝ) ≤ logScale q := by exact_mod_cast logScale_pos q
  have hd' : (rowDepthAt gs I : ℝ) ≤ 10*((logScale q : ℝ)+1) := by exact_mod_cast hd
  push_cast
  nlinarith [Real.sqrt_nonneg (touchingCost (occurrenceSupport gs) I)]

/-- The body of the accepted `Packets.coordinateDegree occ I den`, as twice the
walk length times the window sum. -/
theorem coordinateDegree_at_eq {q : ℕ} (gs : List (SupportedNormalizedGate q)) (I : Finset (Fin q))
    (den : ℕ) :
    canonicalWalkLength den * structuralListCoordinateRawDegree
        (canonicalGradedDepth (touchingCost (occurrenceSupport gs) I))
        (executableGradedWindow (touchingCost (occurrenceSupport gs) I)) gradedTerminalWindow =
      2*canonicalWalkLength den*windowSumAt gs I := by
  unfold windowSumAt rowDepthAt
  rw [rawDegree_window_sum]
  ring

end
end NearCubicWires.RepairSource.CloseoutRawRows
