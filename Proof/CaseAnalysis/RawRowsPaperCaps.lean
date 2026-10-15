import Proof.CaseAnalysis.RawRowsPaperMargin

/-! Per-circuit paper wire caps feed the same actual occurrence pool and
TouchingSelect. Powers5/9 give the squared-load powers4/8 exactly. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open SupplierPipeline SupplierEstimator SupplierTouching
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem list_log_cap {α : Type} (xs : List α) (wires : α → ℕ) (logarithm : ℝ)
    (p : ℕ) (bound : ℝ) (hcap : ∀ c∈xs,(wires c : ℝ)*logarithm^p ≤ bound) :
    (((xs.map wires).sum : ℕ) : ℝ)*logarithm^p ≤ xs.length*bound := by
  induction xs with
  | nil => simp
  | cons c xs ih =>
    have hc := hcap c (by simp)
    have ht := ih (fun c hc => hcap c (by simp [hc]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith only [hc,ht]

theorem wireScale_cap (q p : ℕ) (a : ℝ) (w : ℕ) (h : (w : ℝ) ≤ wireScale a p q) :
    (w : ℝ)*(logScale q : ℝ)^p ≤ a*(q : ℝ)^3 := by
  have hl : (0 : ℝ) < logScale q := by exact_mod_cast logScale_pos q
  exact (le_div_iff₀ (pow_pos hl p)).mp h

theorem symmetric_wire_cap (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (p : ℕ) (a : ℝ) (ha : 0 ≤ a) (hfour : r.circuits.length ≤ 4)
    (hcap : ∀ c∈r.circuits,(c.wireCount : ℝ) ≤ wireScale a p r.q) :
    (occurrenceWireCount (symmetricFourfoldOccurrences r) : ℝ)*(logScale r.q : ℝ)^p ≤
      4*a*(r.q : ℝ)^3 := by
  have hb := list_log_cap r.circuits (fun c => c.wireCount) (logScale r.q) p (a*(r.q : ℝ)^3)
    (fun c hc => wireScale_cap r.q p a c.wireCount (hcap c hc))
  have hw : (occurrenceWireCount (symmetricFourfoldOccurrences r) : ℝ) ≤
      (batchDescription NormalizedSymmetricThresholdCircuit.wireCount r.circuits : ℝ) := by
    exact_mod_cast symmetricFourfoldOccurrences_wireCount_le r
  have hfourR : (r.circuits.length : ℝ) ≤ 4 := by exact_mod_cast hfour
  calc
    _ ≤ (batchDescription NormalizedSymmetricThresholdCircuit.wireCount r.circuits : ℝ)*
        (logScale r.q : ℝ)^p := mul_le_mul_of_nonneg_right hw (by positivity)
    _ ≤ r.circuits.length*(a*(r.q : ℝ)^3) := hb
    _ ≤ _ := by nlinarith [mul_nonneg ha (show 0 ≤ (r.q : ℝ)^3 by positivity)]

theorem threshold_wire_cap (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (p : ℕ) (a : ℝ) (ha : 0 ≤ a) (hfour : r.circuits.length ≤ 4)
    (hcap : ∀ c∈r.circuits,(c.wireCount : ℝ) ≤ wireScale a p r.q) :
    (occurrenceWireCount (thresholdFourfoldOccurrences r) : ℝ)*(logScale r.q : ℝ)^p ≤
      4*a*(r.q : ℝ)^3 := by
  have hb := list_log_cap r.circuits (fun c => c.wireCount) (logScale r.q) p (a*(r.q : ℝ)^3)
    (fun c hc => wireScale_cap r.q p a c.wireCount (hcap c hc))
  have hw : (occurrenceWireCount (thresholdFourfoldOccurrences r) : ℝ) ≤
      (batchDescription NormalizedThresholdThresholdCircuit.wireCount r.circuits : ℝ) := by
    exact_mod_cast thresholdFourfoldOccurrences_wireCount_le r
  have hfourR : (r.circuits.length : ℝ) ≤ 4 := by exact_mod_cast hfour
  calc
    _ ≤ (batchDescription NormalizedThresholdThresholdCircuit.wireCount r.circuits : ℝ)*
        (logScale r.q : ℝ)^p := mul_le_mul_of_nonneg_right hw (by positivity)
    _ ≤ r.circuits.length*(a*(r.q : ℝ)^3) := hb
    _ ≤ _ := by nlinarith [mul_nonneg ha (show 0 ≤ (r.q : ℝ)^3 by positivity)]

theorem touching_log_cap {q : ℕ} (gs : List (SupportedNormalizedGate q))
    (kappa r : ℕ) (a : ℝ) (hq : 0 < q) (hk : 0 < kappa)
    (hcap : (occurrenceWireCount gs : ℝ)*(logScale q : ℝ)^(2*r+5) ≤ 4*a*(q : ℝ)^3) :
    (touchingCost (occurrenceSupport gs) (normalizedLiveSet gs kappa) : ℝ)*
        (logScale q : ℝ)^(2*r+4) ≤ 4*kappa*a*(q : ℝ)^2 := by
  have hl : (0 : ℝ) < logScale q := by exact_mod_cast logScale_pos q
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have ht := normalizedLiveSet_touchingCost gs kappa hq hk
  rw [supportIncidenceMass_occurrenceSupport] at ht
  have hK : normalizedLiveCount q kappa ≤ kappa*logScale q := Nat.min_le_right _ _
  have ht' : (q : ℝ)*touchingCost (occurrenceSupport gs) (normalizedLiveSet gs kappa) ≤
      (kappa*(logScale q : ℝ))*occurrenceWireCount gs := by
    exact_mod_cast ht.trans (Nat.mul_le_mul_right _ hK)
  apply le_of_mul_le_mul_left (a := (q : ℝ)*logScale q) ?_ (mul_pos hqR hl)
  calc
    ((q : ℝ)*logScale q)*
        ((touchingCost (occurrenceSupport gs) (normalizedLiveSet gs kappa) : ℝ)*
          (logScale q : ℝ)^(2*r+4)) =
      ((q : ℝ)*touchingCost (occurrenceSupport gs) (normalizedLiveSet gs kappa))*
        (logScale q : ℝ)^(2*r+5) := by
          rw [show 2*r+5=(2*r+4)+1 by omega,pow_succ']; ring
    _ ≤ ((kappa : ℝ)*logScale q)*occurrenceWireCount gs*(logScale q : ℝ)^(2*r+5) :=
      mul_le_mul_of_nonneg_right ht' (by positivity)
    _ = ((kappa : ℝ)*logScale q)*((occurrenceWireCount gs : ℝ)*(logScale q : ℝ)^(2*r+5)) := by ring
    _ ≤ ((kappa : ℝ)*logScale q)*(4*a*(q : ℝ)^3) :=
      mul_le_mul_of_nonneg_left hcap (by positivity)
    _ = ((q : ℝ)*logScale q)*(4*kappa*a*(q : ℝ)^2) := by ring

theorem symmetric_active_cap (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (kappa : ℕ) (a : ℝ) (ha : 0 ≤ a) (hq : 0 < r.q) (hk : 0 < kappa)
    (hfour : r.circuits.length ≤ 4)
    (hcap : ∀ c∈r.circuits,(c.wireCount : ℝ) ≤ wireScale a 5 r.q) :
    (touchingCost (occurrenceSupport (symmetricFourfoldOccurrences r))
      (normalizedLiveSet (symmetricFourfoldOccurrences r) kappa) : ℝ)*(logScale r.q : ℝ)^4 ≤
      4*kappa*a*(r.q : ℝ)^2 :=
  touching_log_cap _ kappa 0 a hq hk (symmetric_wire_cap r 5 a ha hfour hcap)

theorem threshold_active_cap (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (kappa : ℕ) (a : ℝ) (ha : 0 ≤ a) (hq : 0 < r.q) (hk : 0 < kappa)
    (hfour : r.circuits.length ≤ 4)
    (hcap : ∀ c∈r.circuits,(c.wireCount : ℝ) ≤ wireScale a 9 r.q) :
    (touchingCost (occurrenceSupport (thresholdFourfoldOccurrences r))
      (normalizedLiveSet (thresholdFourfoldOccurrences r) kappa) : ℝ)*(logScale r.q : ℝ)^8 ≤
      4*kappa*a*(r.q : ℝ)^2 :=
  touching_log_cap _ kappa 2 a hq hk (threshold_wire_cap r 9 a ha hfour hcap)

end
end NearCubicWires.RepairSource.CloseoutRawRows
