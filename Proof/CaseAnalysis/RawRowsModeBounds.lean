import Proof.CaseAnalysis.RawRowsChildLog

/-! Actual mode factors for the raw row load. Polynomial accuracy and prime
cutoffs cost one logarithm each; the SYM walk remains a fixed constant. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open SupplierPipeline SupplierEstimator SupplierPrime SupplierWalkBridge
open RepairRepresentation PolynomialSchedule SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem walk_bits (den : ℕ) : canonicalWalkLength den+1 ≤ 2*(natBitLength den+1) := by
  have hlt : den < 2^natBitLength den := by
    simpa only [natBitLength] using Nat.lt_pow_succ_log_self (b := 2) (by decide) den
  have hc := Nat.clog_le_of_le_pow (Nat.succ_le_of_lt hlt)
  change Nat.clog 2 (den+1) ≤ natBitLength den at hc
  unfold canonicalWalkLength
  omega

theorem polynomial_walk_log {den : ℕ → ℕ} (hd : PolynomiallyBounded den) :
    ∃ c : ℕ, 0 < c ∧ ∀ q, canonicalWalkLength (den q)+1 ≤ c*logScale q := by
  obtain ⟨c,hc,h⟩ := polynomial_bits_log hd
  refine ⟨2*c,by omega,?_⟩
  intro q
  exact (walk_bits (den q)).trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 (h q))

theorem primeCutoff_polynomial {exponent den : ℕ → ℕ}
    (he : PolynomiallyBounded exponent) (hd : PolynomiallyBounded den) :
    PolynomiallyBounded (fun q=>canonicalPrimeCutoff (exponent q) (den q)) := by
  have h1 := polynomiallyBounded_constant 1
  exact polynomiallyBounded_pow
    (polynomiallyBounded_max (polynomiallyBounded_constant 24)
      (polynomiallyBounded_mul (polynomiallyBounded_mul (polynomiallyBounded_constant 6)
        (polynomiallyBounded_add he h1)) (polynomiallyBounded_add hd h1))) 2

theorem polynomial_prime_digits_log {cutoff : ℕ → ℕ} (hp : PolynomiallyBounded cutoff) :
    ∃ c : ℕ, 0 < c ∧ ∀ q (prime : PrimeIndex (cutoff q)),
      modulusDigitCount prime.val+1 ≤ c*logScale q := by
  obtain ⟨c,hc,h⟩ := polynomial_bits_log hp
  refine ⟨c,hc,?_⟩
  intro q prime
  have hprime := (mem_primesUpTo.mp prime.property).2
  exact (Nat.add_le_add_right (PolynomialClock.natBitLength_mono hprime) 1).trans (h q)

theorem wire_le_cube {q p w : ℕ} {a : ℝ} (ha : a ≤ 1)
    (hw : (w : ℝ) ≤ wireScale a p q) : w ≤ q^3 := by
  have hl : (1 : ℝ) ≤ logScale q := by exact_mod_cast logScale_pos q
  have hb := wireScale_cap q p a w hw
  have hp : (1 : ℝ) ≤ (logScale q : ℝ)^p := one_le_pow₀ hl
  have hleft : (w : ℝ) ≤ (w : ℝ)*(logScale q : ℝ)^p :=
    le_mul_of_one_le_right (Nat.cast_nonneg w) hp
  have hright : a*(q : ℝ)^3 ≤ (q : ℝ)^3 := by nlinarith [show 0 ≤ (q : ℝ)^3 by positivity]
  exact_mod_cast hleft.trans (hb.trans hright)

theorem symmetric_population (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (p : ℕ) (a : ℝ) (ha : a ≤ 1) (hfour : r.circuits.length ≤ 4)
    (hw : ∀ c∈r.circuits,(c.wireCount : ℝ) ≤ wireScale a p r.q) :
    (symmetricFourfoldOccurrences r).length ≤ 4*r.q^3 := by
  have hsum := batchDescription_le_card_mul NormalizedSymmetricThresholdCircuit.wireCount
    r.circuits (r.q^3) (fun c hc=>wire_le_cube ha (hw c hc))
  have he := symmetricFourfoldOccurrences_wireCount r
  exact (show (symmetricFourfoldOccurrences r).length ≤
    batchDescription NormalizedSymmetricThresholdCircuit.wireCount r.circuits by omega).trans
      (hsum.trans (Nat.mul_le_mul_right _ hfour))

theorem threshold_population (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (p : ℕ) (a : ℝ) (ha : a ≤ 1) (hfour : r.circuits.length ≤ 4)
    (hw : ∀ c∈r.circuits,(c.wireCount : ℝ) ≤ wireScale a p r.q) :
    (thresholdFourfoldOccurrences r).length ≤ 4*r.q^3 := by
  have hsum := batchDescription_le_card_mul NormalizedThresholdThresholdCircuit.wireCount
    r.circuits (r.q^3) (fun c hc=>wire_le_cube ha (hw c hc))
  have he := thresholdFourfoldOccurrences_wireCount r
  exact (show (thresholdFourfoldOccurrences r).length ≤
    batchDescription NormalizedThresholdThresholdCircuit.wireCount r.circuits by omega).trans
      (hsum.trans (Nat.mul_le_mul_right _ hfour))

theorem population_bits_log :
    ∃ c : ℕ, 0 < c ∧ ∀ q pop, pop ≤ 4*q^3 → natBitLength (2*pop+1)+1 ≤ c*logScale q := by
  have hp : PolynomiallyBounded (fun q=>2*(4*q^3)+1) :=
    polynomiallyBounded_add (polynomiallyBounded_mul (polynomiallyBounded_constant 2)
      (polynomiallyBounded_mul (polynomiallyBounded_constant 4)
        (polynomiallyBounded_pow polynomiallyBounded_id 3))) (polynomiallyBounded_constant 1)
  obtain ⟨c,hc,h⟩ := polynomial_bits_log hp
  refine ⟨c,hc,?_⟩
  intro q pop hpop
  exact (Nat.add_le_add_right (PolynomialClock.natBitLength_mono (by omega : 2*pop+1 ≤ 2*(4*q^3)+1)) 1).trans (h q)

end
end NearCubicWires.RepairSource.CloseoutRawRows
