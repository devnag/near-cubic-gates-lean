import Proof.Hierarchy.CompetitorSourceValidity
import Proof.Foundations.RecoveryCaseOne

/-! Paper C.10--C.12 parameter order: retain the source's rational validity
radius, choose the cutoff after the absolute STV exponent, and only then
choose one constant XOR count covering both strict advantage and actual
amplifier arity. No input-dependent repetition count is introduced. -/
namespace NearCubicWires.RepairSource.CloseoutParameters
open SourceInterfaces RepairRepresentation CompetitorRationalGap RecoveryScheduleEnvelope
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem radius_lt_half {source : PointwisePCPPAlgorithm} (constants : Constants source) :
    (zeta constants : ℝ) < 1 / 2 := by
  have hs : 0 < (constants.soundness : ℝ) := source.soundnessPositive.trans constants.lower
  have hc : (constants.completeness : ℝ) < 1 := constants.upper.trans source.completenessBelowOne
  have hg : (constants.soundness : ℝ) < constants.completeness := by exact_mod_cast constants.separation
  have hsquare : ((constants.completeness : ℝ)-constants.soundness)^2 < 1 := by nlinarith
  simp only [zeta,gap,Rat.cast_div,Rat.cast_pow,Rat.cast_sub,Rat.cast_ofNat]
  linarith

theorem constant_copies (delta : ℚ) (hd : 0 < delta) (hh : (delta : ℝ)≤1/2)
    (gamma : ℝ) (hg : 0 < gamma) (arityCoefficient : Nat) :
    ∃ copies : Nat, 1≤copies ∧ arityCoefficient≤copies ∧
      xorEpsilon (delta : ℝ) copies < gamma := by
  obtain ⟨a,ha⟩ := exists_nat_one_div_lt hg
  let rate:=max a arityCoefficient
  refine ⟨fixedCopiesOf delta rate,fixedCopiesOf_positive delta rate,?_,?_⟩
  · have hd1 : 1≤recoveryBlockOf delta := recoveryBlockOf_positive delta
    have hr : arityCoefficient≤rate := Nat.le_max_right _ _
    unfold fixedCopiesOf
    nlinarith
  · have hpow : (rate+1 : ℝ)≤(2 : ℝ)^rate := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self : rate < 2^rate)
    have hr : (a+1 : ℝ)≤rate+1 := by exact_mod_cast Nat.add_le_add_right (Nat.le_max_left a arityCoefficient) 1
    have hdiv : 1/(2 : ℝ)^rate ≤ 1/(rate+1 : ℝ) :=
      one_div_le_one_div_of_le (by positivity) hpow
    have hdiv2 : 1/(rate+1 : ℝ)≤1/(a+1 : ℝ) :=
      one_div_le_one_div_of_le (by positivity) hr
    have he:=xorEpsilon_fixedCopiesOf_le hd hh rate
    have hp : 0≤1/(2 : ℝ)^rate := by positivity
    linarith

theorem arity_envelope {c d : Nat} (amplifier : OrdinaryScheduleAmplifier c d)
    (copies q r : Nat) (hc : amplifier.arityCoefficient≤copies) (hq : 1≤q)
    (f : BoolFunction q) :
    (amplifier.output q f).arity≤copies*(q+r+1) :=
  (amplifier.arityBound q f hq).trans (Nat.mul_le_mul hc (by omega))

theorem fixed_parameters (factory : SourceAmplifierFactory) (simulationPower : Nat)
    (delta : ℚ) (hd : 0 < delta) (hh : (delta : ℝ)≤1/2)
    (gamma : ℝ) (hg : 0 < gamma) :
    ∃ degree copies : Nat,
      (simulationPower+1)*factory.stvExponent < degree ∧ 1≤copies ∧
      xorEpsilon (delta : ℝ) copies < gamma ∧
      ∀ q r (f : BoolFunction q), 1≤q →
        ((selectedAmplifier factory degree).output q f).arity≤copies*(q+r+1) := by
  let degree:=(simulationPower+2)*factory.stvExponent
  let amplifier:=selectedAmplifier factory degree
  obtain ⟨copies,hcopies,hcover,heps⟩ := constant_copies delta hd hh gamma hg amplifier.arityCoefficient
  refine ⟨degree,copies,?_,hcopies,heps,?_⟩
  · have hp:=factory.stvExponentPositive
    dsimp only [degree]
    nlinarith
  · intro q r f hq
    exact arity_envelope amplifier copies q r hcover hq f

end NearCubicWires.RepairSource.CloseoutParameters
