import Proof.CaseAnalysis.ScheduleBounds
import Proof.CaseAnalysis.Parameters
import Proof.Amplification.CaseOneRecoveryAssembly

/-! Apply the existing physical simulation bound at the actual final length.
One extra power of q pays the fixed schedule factor after a finite onset;
the absolute STV exponent still precedes the selected amplifier. -/
namespace NearCubicWires.RepairSource.CloseoutCaseOne
open RecoveryScheduleEnvelope CaseOneRecoveryAssembly SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem simulation_bound (c d factor n q logExponent : Nat)
    (hc : 0 < c) (hq : 0 < q) (hn : 6 ≤ n)
    (hnq : n ≤ factor*q) (hfactor : factor^16 ≤ q) (hd : 17*c ≤ d)
    {coefficient : ℝ} (hzero : 0 ≤ coefficient) (hone : coefficient ≤ 1) :
    50*(n+⌊wireScale coefficient logExponent n⌋₊+2)^4 ≤
      integerFloorRoot c (oracleSizeBound d q) := by
  have hs:=simulationCost_le_power 50 logExponent n le_rfl hn hzero hone
  have hp : n^16 ≤ q^17 := by
    calc
      n^16 ≤ (factor*q)^16 := Nat.pow_le_pow_left hnq 16
      _ = factor^16*q^16 := mul_pow _ _ _
      _ ≤ q*q^16 := Nat.mul_le_mul_right _ hfactor
      _ = q^17 := by rw [show 17=16+1 by rfl,pow_succ q 16,Nat.mul_comm]
  exact hs.trans (hp.trans (amplifier_size_ge_power c d 17 q hc hq hd))

theorem advantage_onset (c d : Nat) (hc : 0 < c) (hd : c ≤ d)
    (gamma : ℝ) (hg : 0 < gamma) :
    ∃ onset : Nat, 1 ≤ onset ∧ ∀ q, onset ≤ q →
      Real.rpow (oracleSizeBound d q : ℝ) (-(1 : ℝ)/c) < gamma := by
  obtain ⟨a,ha⟩:=exists_nat_one_div_lt hg
  refine ⟨a+1,by omega,?_⟩
  intro q hq
  have h:=amplifier_advantage_le_power c d 1 q hc (by omega) (by simpa using hd)
  have hid : inversePolynomialAdvantage q (1 : ℝ)=(1 : ℝ)/q := by
    simp [inversePolynomialAdvantage,Real.rpow_neg_one]
  norm_num only [Nat.cast_one] at h
  rw [hid] at h
  have hr : (a+1 : ℝ) ≤ q := by exact_mod_cast hq
  have hi : (1 : ℝ)/q ≤ 1/(a+1 : ℝ) := one_div_le_one_div_of_le (by positivity) hr
  exact h.trans_lt (hi.trans_lt ha)

theorem length_native_factor (copies degree q n : Nat) (hq : 1 ≤ q)
    (hcore : n/3 ≤ CloseoutLanguage.coreWidth copies degree q) :
    n ≤ (3*(copies*(2*degree+2))+2)*q := by
  have hu:=CloseoutLanguage.core_upper copies degree q hq
  have hn : n ≤ 3*(n/3)+2 := by omega
  nlinarith

end NearCubicWires.RepairSource.CloseoutCaseOne
