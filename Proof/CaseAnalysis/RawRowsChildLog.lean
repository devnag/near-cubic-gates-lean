import Proof.CaseAnalysis.RawRowsPaperCaps
import Proof.CaseAnalysis.WitnessPolicy

/-! The actual description guard bounds source children logarithmically in
q. The strict-threshold decrement adds at most one encoding bit. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open SupplierPipeline SupplierEstimator CompilerSemantics SourceInterfaces
open RepairRepresentation PolynomialSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem bits_two_pow (k : ℕ) : natBitLength (2^k)=k+1 := by
  unfold natBitLength
  rw [Nat.log_pow (by omega)]

theorem bits_succ (n : ℕ) : natBitLength (n+1) ≤ natBitLength n+1 := by
  have hlt : n < 2^natBitLength n := by
    simpa only [natBitLength] using Nat.lt_pow_succ_log_self (b := 2) (by omega) n
  exact (PolynomialClock.natBitLength_mono hlt).trans (by rw [bits_two_pow])

theorem strict_gate_bits {q : ℕ} (g : NormalizedThresholdGate q) :
    (nonStrictAsStrict g).encodingBits ≤ g.encodingBits+1 := by
  have hm : (g.threshold-1).natAbs ≤ g.threshold.natAbs+1 := by
    simpa only [sub_eq_add_neg,Int.natAbs_neg,Int.natAbs_one] using Int.natAbs_add_le g.threshold (-1)
  have hb := (PolynomialClock.natBitLength_mono hm).trans (bits_succ g.threshold.natAbs)
  change intBitLength (g.threshold-1) ≤ intBitLength g.threshold+1 at hb
  unfold NormalizedThresholdGate.encodingBits nonStrictAsStrict
  dsimp only
  omega

def sourceChildBound (a : DecompositionAlgorithm) (descriptionCap : ℕ) :=
  a.coefficient*(descriptionCap+2)^a.degree

theorem source_children_le {q : ℕ} (a : DecompositionAlgorithm)
    (gs : List (SupportedNormalizedGate q)) (descriptionCap : ℕ)
    (hdesc : ∀ i, (gs.get i).descriptionBits ≤ descriptionCap) (i : Fin gs.length) :
    (occurrenceExactChildren a gs i).length ≤ sourceChildBound a descriptionCap := by
  have hb := strict_gate_bits (gs.get i).gate
  have hd := hdesc i
  have hparam : q+(nonStrictAsStrict (gs.get i).gate).encodingBits+1 ≤ descriptionCap+2 := by
    unfold SupportedNormalizedGate.descriptionBits at hd
    omega
  exact (actual_children_bound a gs i).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hparam a.degree))

theorem sourceChildBound_polynomial (a : DecompositionAlgorithm) {f : ℕ → ℕ}
    (hf : PolynomiallyBounded f) : PolynomiallyBounded (fun q=>sourceChildBound a (f q)) :=
  polynomiallyBounded_mul (polynomiallyBounded_constant a.coefficient)
    (polynomiallyBounded_pow (polynomiallyBounded_add hf (polynomiallyBounded_constant 2)) a.degree)

theorem polynomial_bits_log {f : ℕ → ℕ} (hf : PolynomiallyBounded f) :
    ∃ c : ℕ, 0 < c ∧ ∀ q, natBitLength (f q)+1 ≤ c*logScale q := by
  obtain ⟨C,d,_hC,hbound⟩ := hf
  refine ⟨C+2*d+4,by omega,?_⟩
  intro q
  have hlog : 1 ≤ logScale q := logScale_pos q
  have hbitsC : natBitLength C ≤ C+1 := by
    unfold natBitLength
    have h := Nat.log_le_self 2 C
    omega
  have hq : q+1 ≤ 2^logScale q :=
    (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) (q+2))
  have hqb := PolynomialClock.natBitLength_mono hq
  rw [bits_two_pow] at hqb
  have hb := (PolynomialClock.natBitLength_mono (hbound q)).trans
    (ValidatorPolynomialDomination.natBitLength_mul_le C ((q+1)^d))
  have hp := ValidatorPolynomialDomination.natBitLength_pow_le (q+1) d
  have hd := Nat.mul_le_mul_left d hqb
  have hsmall := Nat.mul_le_mul_left (C+d+3) hlog
  nlinarith

theorem child_log_envelope (a : DecompositionAlgorithm) {descriptionCap : ℕ → ℕ}
    (hcap : PolynomiallyBounded descriptionCap) :
    ∃ c : ℕ, 0 < c ∧ ∀ q (gs : List (SupportedNormalizedGate q)),
      (∀ i, (gs.get i).descriptionBits ≤ descriptionCap q) →
      ∀ i, (occurrenceExactChildren a gs i).length < 2^(c*logScale q) := by
  obtain ⟨c,hc,he⟩ := polynomial_bits_log (sourceChildBound_polynomial a hcap)
  refine ⟨c,hc,?_⟩
  intro q gs hdesc i
  have hlt : sourceChildBound a (descriptionCap q) < 2^natBitLength (sourceChildBound a (descriptionCap q)) := by
    simpa only [natBitLength] using Nat.lt_pow_succ_log_self (b := 2) (by omega) (sourceChildBound a (descriptionCap q))
  exact (source_children_le a gs _ hdesc i).trans_lt
    (hlt.trans_le (Nat.pow_le_pow_right (by decide) (by have h := he q; omega)))

end
end NearCubicWires.RepairSource.CloseoutRawRows
