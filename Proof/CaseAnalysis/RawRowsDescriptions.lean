import Proof.CaseAnalysis.RawRowsChildLog

/-! The actual restricted mode descriptions have one coarse polynomial
envelope, chosen before the live saving and small wire-cap coefficient. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open SupplierPipeline SupplierEstimator SourceInterfaces RepairRepresentation
open PolynomialSchedule ComponentwiseCircuitRestriction RecoveryWitnessPolicy
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev symmetricDescription (q n W : ℕ) :=
  restrictedSymmetricDescriptionCap q n (2^symmetricDescriptionCap n W) W
abbrev thresholdDescription (q n W : ℕ) :=
  restrictedThresholdDescriptionCap q n (2^thresholdDescriptionCap n W) (thresholdDescriptionCap n W)

theorem restricted_gate_mono {q n a b : ℕ} (hab : a ≤ b) :
    restrictedGateDescriptionCap q n a ≤ restrictedGateDescriptionCap q n b := by
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _
    (PolynomialClock.natBitLength_mono (Nat.mul_le_mul_left _ hab))) _

theorem symmetric_description_mono {q n W V : ℕ} (hW : W ≤ V) :
    symmetricDescription q n W ≤ symmetricDescription q n V := by
  have hb : symmetricDescriptionCap n W ≤ symmetricDescriptionCap n V :=
    Nat.mul_le_mul_right _ (Nat.add_le_add_right hW 1)
  exact Nat.mul_le_mul (Nat.add_le_add_right hW 1)
    (Nat.add_le_add_right (restricted_gate_mono (Nat.pow_le_pow_right (by decide) hb)) 1)

theorem threshold_description_mono {q n W V : ℕ} (hW : W ≤ V) :
    thresholdDescription q n W ≤ thresholdDescription q n V := by
  have hb : thresholdDescriptionCap n W ≤ thresholdDescriptionCap n V :=
    Nat.add_le_add (normalizedGateDescriptionCap_mono hW) (Nat.mul_le_mul_right _ hW)
  exact Nat.mul_le_mul (Nat.add_le_add_right hb 1)
    (Nat.add_le_add_right (restricted_gate_mono (Nat.pow_le_pow_right (by decide) hb)) 1)

def descriptionEnvelope (degree q : ℕ) :=
  let n := q+CloseoutLanguage.clauseWidth degree q+1
  max (symmetricDescription q n (q^3)) (thresholdDescription q n (q^3))

theorem descriptionEnvelope_polynomial (degree : ℕ) :
    PolynomiallyBounded (descriptionEnvelope degree) := by
  have hr : PolynomiallyBounded (CloseoutLanguage.clauseWidth degree) :=
    polynomiallyBounded_mono (CloseoutLanguage.clause_linear degree)
      (polynomiallyBounded_mul (polynomiallyBounded_constant degree)
        (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1)))
  have hn := polynomiallyBounded_add (polynomiallyBounded_add polynomiallyBounded_id hr)
    (polynomiallyBounded_constant 1)
  have hW := polynomiallyBounded_pow polynomiallyBounded_id 3
  exact polynomiallyBounded_max
    (CloseoutWitnessResources.restricted_symmetric_polynomial polynomiallyBounded_id hn hW)
    (CloseoutWitnessResources.restricted_threshold_polynomial polynomiallyBounded_id hn hW)

theorem actual_description_envelope (degree q W : ℕ) (hW : W ≤ q^3) :
    symmetricDescription q (q+CloseoutLanguage.clauseWidth degree q+1) W ≤ descriptionEnvelope degree q ∧
    thresholdDescription q (q+CloseoutLanguage.clauseWidth degree q+1) W ≤ descriptionEnvelope degree q :=
  ⟨(symmetric_description_mono hW).trans (Nat.le_max_left _ _),
   (threshold_description_mono hW).trans (Nat.le_max_right _ _)⟩

theorem symmetric_occurrences_description
    (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (cap : ℕ)
    (hcap : ∀ c∈r.circuits,c.descriptionBits ≤ cap) :
    ∀ i, ((symmetricFourfoldOccurrences r).get i).descriptionBits ≤ cap := by
  have hall : ∀ g∈symmetricFourfoldOccurrences r,g.descriptionBits ≤ cap := by
    intro g hg
    obtain ⟨c,hc,hg⟩ := List.mem_flatMap.mp hg
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hg
    have hb := Finset.single_le_sum (fun j _=>Nat.zero_le (c.bottom j).descriptionBits) (Finset.mem_univ i)
    have hd := hcap c hc
    unfold NormalizedSymmetricThresholdCircuit.descriptionBits at hd
    omega
  intro i
  exact hall _ (List.get_mem _ _)

theorem threshold_occurrences_description
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (cap : ℕ)
    (hcap : ∀ c∈r.circuits,c.descriptionBits ≤ cap) :
    ∀ i, ((thresholdFourfoldOccurrences r).get i).descriptionBits ≤ cap := by
  have hall : ∀ g∈thresholdFourfoldOccurrences r,g.descriptionBits ≤ cap := by
    intro g hg
    obtain ⟨c,hc,hg⟩ := List.mem_flatMap.mp hg
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hg
    have hb := Finset.single_le_sum (fun j _=>Nat.zero_le (c.bottom j).descriptionBits)
      (Finset.mem_univ (retainedTopIndex c i))
    have hd := hcap c hc
    unfold NormalizedThresholdThresholdCircuit.descriptionBits at hd
    omega
  intro i
  exact hall _ (List.get_mem _ _)

theorem actual_children_log (a : DecompositionAlgorithm) (degree : ℕ) :
    ∃ c : ℕ, 0 < c ∧ ∀ q (gs : List (SupportedNormalizedGate q)),
      (∀ i, (gs.get i).descriptionBits ≤ descriptionEnvelope degree q) →
      ∀ i, (occurrenceExactChildren a gs i).length < 2^(c*logScale q) :=
  child_log_envelope a (descriptionEnvelope_polynomial degree)

end
end NearCubicWires.RepairSource.CloseoutRawRows
