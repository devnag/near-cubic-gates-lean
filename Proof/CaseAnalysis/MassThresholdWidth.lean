import Proof.CaseAnalysis.WitnessCoefficientPolicy
import Proof.CaseAnalysis.SampledWitness
import Proof.Hierarchy.CompetitorThresholdDecision
import Proof.Hierarchy.CompetitorSumWidth

/-! The fixed exact mass threshold already fits the produced coefficient
width. Its reduced fraction is bounded by the original rational parameters;
no extra input cutoff, larger mass cap or runtime width test is required. -/
namespace NearCubicWires.RepairSource.CloseoutMassThreshold
open RepairOrdinary RepairRepresentation RepairXor CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rawDen (a b j : Nat) := (b-a)^(j-1)*(b-2*a)
def literalWidth (delta : ℚ) (copies : Nat) := natBitLength (2*delta.den^copies)

theorem raw_bounds (a b j : Nat) (hab : 2*a < b) (hj : 1 ≤ j) :
    0 < rawDen a b j ∧ rawDen a b j ≤ 2*b^j := by
  have hb : 0 < b := by omega
  have hba : 0 < b-a := by omega
  have hbaa : 0 < b-2*a := by omega
  have hp : b^(j-1)*b=b^j := by rw [←pow_succ,show j-1+1=j by omega]
  constructor
  · exact Nat.mul_pos (Nat.pow_pos hba) hbaa
  · have h := Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.sub_le b a) (j-1)) (Nat.sub_le b (2*a))
    change rawDen a b j ≤ b^(j-1)*b at h
    rw [hp] at h
    omega

theorem mass_raw (delta : ℚ) (hd : 0 < delta) (hh : delta < 1/2)
    (copies : Nat) (hc : 1 ≤ copies) :
    CloseoutSampledWitness.massCap delta copies=
      ((2*delta.den^copies : Nat) : ℚ)/rawDen delta.num.natAbs delta.den copies := by
  obtain ⟨ha,hab,he⟩ := radius_parameters delta hd hh
  have hb : (0 : ℚ) < delta.den := by exact_mod_cast delta.pos
  have haB : delta.num.natAbs ≤ delta.den := by omega
  have h2aB : 2*delta.num.natAbs ≤ delta.den := by omega
  have hsub : 1-delta=((delta.den-delta.num.natAbs : Nat) : ℚ)/delta.den := by
    conv_lhs => rw [he]
    rw [Nat.cast_sub haB]
    field_simp
  have hhalf : 1/2-delta=((delta.den-2*delta.num.natAbs : Nat) : ℚ)/(2*delta.den) := by
    conv_lhs => rw [he]
    rw [Nat.cast_sub h2aB]
    push_cast
    field_simp
  have hp : (delta.den : ℚ)^(copies-1)*delta.den=(delta.den : ℚ)^copies := by
    rw [←pow_succ,show copies-1+1=copies by omega]
  have heps : epsilonQ delta copies=
      (rawDen delta.num.natAbs delta.den copies : ℚ)/(2*(delta.den : ℚ)^copies) := by
    unfold epsilonQ rawDen
    rw [hsub,hhalf]
    push_cast
    rw [div_pow]
    rw [←hp]
    field_simp
  unfold CloseoutSampledWitness.massCap
  rw [heps,one_div_div]
  push_cast
  rfl

theorem threshold_fits (delta : ℚ) (hd : 0 < delta) (hh : delta < 1/2)
    (copies q0 clauseBits : Nat) (hc : 1 ≤ copies) :
    literalWidth delta copies ≤ CoefficientBits.width delta copies q0 clauseBits ∧
      CompetitorThresholdDecision.numerator (CloseoutSampledWitness.massCap delta copies) <
        2^literalWidth delta copies ∧
      (CloseoutSampledWitness.massCap delta copies).den < 2^literalWidth delta copies := by
  obtain ⟨_,hab,_⟩ := radius_parameters delta hd hh
  obtain ⟨hD,hDN⟩ := raw_bounds delta.num.natAbs delta.den copies hab hc
  have hred := fraction_reduction_bounds (2*delta.den^copies : Nat)
    (rawDen delta.num.natAbs delta.den copies) hD
  simp only [Int.natAbs_natCast,Int.cast_natCast] at hred
  rw [←mass_raw delta hd hh copies hc] at hred
  have hp := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (2*delta.den^copies)
  have hexp : delta.den^copies ≤ delta.den^(3*copies+2) :=
    Nat.pow_le_pow_right delta.pos (by omega)
  have hpoly : 2*delta.den^copies ≤
      ProjectionNormalization.DimensionPolynomial.value 1 (CoefficientBits.factor delta copies) q0 := by
    unfold ProjectionNormalization.DimensionPolynomial.value CoefficientBits.factor
    simp only [pow_one]
    nlinarith
  have hbits := ValidatorLeafWidthCore.natBitLength_mono hpoly
  refine ⟨?_,hred.1.trans_lt hp,(hred.2.trans hDN).trans_lt hp⟩
  unfold literalWidth CoefficientBits.width
  omega

theorem shared_fits (delta : ℚ) (hd : 0 < delta) (hh : delta < 1/2)
    (copies q0 clauseBits T : Nat) (hc : 1 ≤ copies) :
    literalWidth delta copies ≤ CompetitorSumWidth.width T
      (natBitLength (CloseoutXor.cap delta q0 copies*max 1 (2*2^clauseBits))) := by
  have h := (threshold_fits delta hd hh copies q0 clauseBits hc).1
  rw [CoefficientBits.exact_bits]
  unfold CompetitorSumWidth.width
  change literalWidth delta copies ≤ (T+1)*(CoefficientBits.width delta copies q0 clauseBits+1)
  nlinarith

end NearCubicWires.RepairSource.CloseoutMassThreshold
