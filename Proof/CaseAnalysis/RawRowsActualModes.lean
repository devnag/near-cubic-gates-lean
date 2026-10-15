import Proof.CaseAnalysis.RawRowsModeGate
import Proof.CaseAnalysis.RawRowsThresholdAccuracy

/-! Actual mode caps close the raw printer's quantitative gate. Source
description/accuracy constants precede κ; positive caps and onsets follow it. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open SupplierPipeline SupplierEstimator SupplierWalkBridge SupplierTouching SupplierPrime
open SourceInterfaces RepairRepresentation PolynomialSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem symmetric_paper_margin (a : DecompositionAlgorithm) (degree kappa den : ℕ)
    (hk : 0 < kappa) :
    ∃ (ce : ℕ) (cap : ℝ) (onset : ℕ), 0 < ce ∧ 0 < cap ∧ cap ≤ 1 ∧
      ∀ r : FourfoldRequest NormalizedSymmetricThresholdCircuit,
        onset ≤ r.q → r.circuits.length ≤ 4 →
        (∀ c∈r.circuits,(c.wireCount : ℝ) ≤ wireScale cap 5 r.q) →
        (∀ c∈r.circuits,c.descriptionBits ≤ descriptionEnvelope degree r.q) →
        let gs := symmetricFourfoldOccurrences r
        natBitLength (2*gs.length+1) ≤ ce*logScale r.q ∧
        (∀ i,(occurrenceExactChildren a gs i).length ≤ 2^(ce*logScale r.q)) ∧
        200*modeLoad gs kappa den r.circuits.length ce ≤ r.q-normalizedLiveCount r.q kappa ∧
        67 ≤ r.q-normalizedLiveCount r.q kappa := by
  obtain ⟨ce,hce,hwidth⟩ := actual_log_bounds a degree
  let t := canonicalWalkLength den
  let A := shapeCoefficient 4 t ce kappa
  let cap := paperCap A kappa
  obtain ⟨onset,hm⟩ := mode_paper_gate kappa ce 4 t 0 0
  refine ⟨ce,cap,max 1 onset,hce,paperCap_positive A kappa,paperCap_le_one A kappa,?_⟩
  intro r hr hfour hw hd
  have hq : 0 < r.q := lt_of_lt_of_le (by decide : 0 < 1) ((Nat.le_max_left _ _).trans hr)
  have hone : cap ≤ 1 := paperCap_le_one A kappa
  have hpop := symmetric_population r 5 cap hone hfour hw
  have hfits := hwidth r.q _ hpop (symmetric_occurrences_description r _ hd)
  refine ⟨hfits.1,hfits.2,?_⟩
  apply hm r.q ((Nat.le_max_right _ _).trans hr) (symmetricFourfoldOccurrences r)
    den r.circuits.length hpop
  · simpa only [pow_zero,Nat.mul_one] using Nat.add_le_add_right hfour 1
  · simp only [pow_zero,Nat.mul_one,t,le_refl]
  · exact symmetric_active_cap r kappa cap (paperCap_positive A kappa).le hq hk hfour hw

theorem threshold_paper_margin (a : DecompositionAlgorithm) (degree kappa : ℕ)
    (target : ℕ → ℕ) (htarget : PolynomiallyBounded target) (hk : 0 < kappa) :
    ∃ (ce : ℕ) (cap : ℝ) (onset : ℕ), 0 < ce ∧ 0 < cap ∧ cap ≤ 1 ∧
      ∀ r : FourfoldRequest NormalizedThresholdThresholdCircuit,
        onset ≤ r.q → r.circuits.length ≤ 4 →
        (∀ c∈r.circuits,(c.wireCount : ℝ) ≤ wireScale cap 9 r.q) →
        (∀ c∈r.circuits,c.descriptionBits ≤ descriptionEnvelope degree r.q) →
        ∀ prime : PrimeIndex (thresholdCutoff a (descriptionEnvelope degree r.q) (target r.q)),
        let gs := thresholdFourfoldOccurrences r
        let den := thresholdListDen a (descriptionEnvelope degree r.q) (target r.q)
        natBitLength (2*gs.length+1) ≤ ce*logScale r.q ∧
        (∀ i,(occurrenceExactChildren a gs i).length ≤ 2^(ce*logScale r.q)) ∧
        200*modeLoad gs kappa den (modulusDigitCount prime.val) ce ≤
          r.q-normalizedLiveCount r.q kappa ∧
        67 ≤ r.q-normalizedLiveCount r.q kappa := by
  obtain ⟨ce,hce,hwidth⟩ := actual_log_bounds a degree
  obtain ⟨cz,ct,_hcz,_hct,hlogs⟩ := threshold_mode_logs a degree target htarget
  let A := shapeCoefficient cz ct ce kappa
  let cap := paperCap A kappa
  obtain ⟨onset,hm⟩ := mode_paper_gate kappa ce cz ct 1 1
  refine ⟨ce,cap,max 1 onset,hce,paperCap_positive A kappa,paperCap_le_one A kappa,?_⟩
  intro r hr hfour hw hd prime
  have hq : 0 < r.q := lt_of_lt_of_le (by decide : 0 < 1) ((Nat.le_max_left _ _).trans hr)
  have hone : cap ≤ 1 := paperCap_le_one A kappa
  have hpop := threshold_population r 9 cap hone hfour hw
  have hfits := hwidth r.q _ hpop (threshold_occurrences_description r _ hd)
  refine ⟨hfits.1,hfits.2,?_⟩
  apply hm r.q ((Nat.le_max_right _ _).trans hr) (thresholdFourfoldOccurrences r)
    (thresholdListDen a (descriptionEnvelope degree r.q) (target r.q))
    (modulusDigitCount prime.val) hpop
  · simpa only [pow_one] using ((hlogs r.q).2 prime).trans
      (Nat.mul_le_mul_right (logScale r.q) (Nat.le_succ cz))
  · simpa only [pow_one] using (hlogs r.q).1.trans
      (Nat.mul_le_mul_right (logScale r.q) (Nat.le_succ ct))
  · exact threshold_active_cap r kappa cap (paperCap_positive A kappa).le hq hk hfour hw

end
end NearCubicWires.RepairSource.CloseoutRawRows
