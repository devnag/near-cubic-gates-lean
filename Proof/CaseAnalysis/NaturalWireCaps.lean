import Proof.CaseAnalysis.RawRowsActualModes
import Mathlib.Algebra.Order.Floor.Semifield

/-! The physical mode guard uses natural division, with one fixed positive
integer denominator. Its accepted cap is exactly the real wireScale floor;
the paper margin permits this choice without computing any real constant. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open SupplierPipeline SupplierEstimator SupplierWalkBridge SupplierTouching SupplierPrime
open SourceInterfaces RepairRepresentation PolynomialSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def naturalWireCap (den exponent q : Nat) := q^3 / (den * logScale q^exponent)

theorem naturalWireCap_floor (den exponent q : Nat) :
    ⌊wireScale (1 / (den : ℝ)) exponent q⌋₊ = naturalWireCap den exponent q := by
  have he : wireScale (1 / (den : ℝ)) exponent q =
      ((q^3 : Nat) : ℝ) / ((den * logScale q^exponent : Nat) : ℝ) := by
    simp only [wireScale, Nat.cast_pow, Nat.cast_mul, div_eq_mul_inv,
      one_mul, mul_inv_rev]
    ring
  rw [he, Nat.floor_div_eq_div]
  rfl

theorem naturalWireCap_le_cube (den exponent q : Nat) :
    naturalWireCap den exponent q ≤ q^3 := Nat.div_le_self _ _

theorem naturalWireCap_le_scale (den exponent q : Nat) :
    (naturalWireCap den exponent q : ℝ) ≤ wireScale (1 / (den : ℝ)) exponent q := by
  rw [← naturalWireCap_floor]
  apply Nat.floor_le
  unfold wireScale
  positivity

theorem exists_reciprocal_subcap {cap : ℝ} (hc : 0 < cap) :
    ∃ den : Nat, 0 < den ∧ 1 / (den : ℝ) ≤ cap := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hc
  exact ⟨n + 1, by omega, by simpa only [Nat.cast_add, Nat.cast_one] using hn.le⟩

theorem symmetric_natural_margin (a : DecompositionAlgorithm) (degree kappa walkDen : Nat)
    (hk : 0 < kappa) :
    ∃ ce den onset : Nat, 0 < ce ∧ 0 < den ∧
      ∀ r : FourfoldRequest NormalizedSymmetricThresholdCircuit,
        onset ≤ r.q → r.circuits.length ≤ 4 →
        (∀ c ∈ r.circuits, c.wireCount ≤ naturalWireCap den 5 r.q) →
        (∀ c ∈ r.circuits, c.descriptionBits ≤ descriptionEnvelope degree r.q) →
        let gs := symmetricFourfoldOccurrences r
        natBitLength (2 * gs.length + 1) ≤ ce * logScale r.q ∧
        (∀ i, (occurrenceExactChildren a gs i).length ≤ 2^(ce * logScale r.q)) ∧
        200 * modeLoad gs kappa walkDen r.circuits.length ce ≤
          r.q - normalizedLiveCount r.q kappa ∧
        67 ≤ r.q - normalizedLiveCount r.q kappa := by
  obtain ⟨ce, cap, onset, hce, hc, _hc1, hm⟩ :=
    symmetric_paper_margin a degree kappa walkDen hk
  obtain ⟨den, hd, hcap⟩ := exists_reciprocal_subcap hc
  refine ⟨ce, den, onset, hce, hd, ?_⟩
  intro r hr hfour hw hdesc
  apply hm r hr hfour _ hdesc
  intro c hc
  have hnat : (c.wireCount : ℝ) ≤ naturalWireCap den 5 r.q := by
    exact_mod_cast hw c hc
  exact hnat.trans ((naturalWireCap_le_scale den 5 r.q).trans
    (wireScale_mono_coefficient hcap 5 r.q))

theorem threshold_natural_margin (a : DecompositionAlgorithm) (degree kappa : Nat)
    (target : Nat → Nat) (htarget : PolynomiallyBounded target) (hk : 0 < kappa) :
    ∃ ce den onset : Nat, 0 < ce ∧ 0 < den ∧
      ∀ r : FourfoldRequest NormalizedThresholdThresholdCircuit,
        onset ≤ r.q → r.circuits.length ≤ 4 →
        (∀ c ∈ r.circuits, c.wireCount ≤ naturalWireCap den 9 r.q) →
        (∀ c ∈ r.circuits, c.descriptionBits ≤ descriptionEnvelope degree r.q) →
        ∀ prime : PrimeIndex (thresholdCutoff a (descriptionEnvelope degree r.q) (target r.q)),
        let gs := thresholdFourfoldOccurrences r
        let walkDen := thresholdListDen a (descriptionEnvelope degree r.q) (target r.q)
        natBitLength (2 * gs.length + 1) ≤ ce * logScale r.q ∧
        (∀ i, (occurrenceExactChildren a gs i).length ≤ 2^(ce * logScale r.q)) ∧
        200 * modeLoad gs kappa walkDen (modulusDigitCount prime.val) ce ≤
          r.q - normalizedLiveCount r.q kappa ∧
        67 ≤ r.q - normalizedLiveCount r.q kappa := by
  obtain ⟨ce, cap, onset, hce, hc, _hc1, hm⟩ :=
    threshold_paper_margin a degree kappa target htarget hk
  obtain ⟨den, hd, hcap⟩ := exists_reciprocal_subcap hc
  refine ⟨ce, den, onset, hce, hd, ?_⟩
  intro r hr hfour hw hdesc prime
  apply hm r hr hfour _ hdesc prime
  intro c hc
  have hnat : (c.wireCount : ℝ) ≤ naturalWireCap den 9 r.q := by
    exact_mod_cast hw c hc
  exact hnat.trans ((naturalWireCap_le_scale den 9 r.q).trans
    (wireScale_mono_coefficient hcap 9 r.q))

end
end NearCubicWires.RepairSource.CloseoutRawRows
