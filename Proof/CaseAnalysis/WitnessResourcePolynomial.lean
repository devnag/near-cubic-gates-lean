import Proof.CaseAnalysis.SampledWitness
import Proof.CaseAnalysis.NativeWidthStep

/-! Polynomial syntax charges for the actual sampled and restricted atoms.
The exponential parameter bound stays inside its bit length. These are code
size estimates; the tighter numeric guard used by the hot scalar is unchanged. -/
namespace NearCubicWires.RepairSource.CloseoutWitnessResources
open SourceInterfaces RepairRepresentation RepairOrdinary
open RecoveryWitnessPolicy ComponentwiseCircuitRestriction PolynomialSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem bits_polynomial {f : Nat→Nat} (hf : PolynomiallyBounded f) :
    PolynomiallyBounded (fun q=>natBitLength (f q)) :=
  polynomiallyBounded_mono (fun q=>Nat.add_le_add_right (Nat.log_le_self 2 (f q)) 1)
    (polynomiallyBounded_add hf (polynomiallyBounded_constant 1))

theorem xor_terms_polynomial (delta : ℚ) (copies : Nat) :
    PolynomiallyBounded (fun n=>xorTermBound delta n copies) := by
  let a : ℝ:=16/((delta : ℝ)^2*xorEpsilon (delta : ℝ) copies^2)
  refine ⟨Nat.ceil a+1,1,by omega,?_⟩
  intro n
  rw [pow_one]
  unfold xorTermBound
  apply Nat.ceil_le.mpr
  have ha : a ≤ (Nat.ceil a : ℝ) := Nat.le_ceil a
  have hc : (0 : ℝ) ≤ Nat.ceil a := Nat.cast_nonneg _
  have hm:=mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have he : 16*(n : ℝ)/((delta : ℝ)^2*xorEpsilon (delta : ℝ) copies^2)=a*n := by
    dsimp [a]
    ring
  rw [he]
  push_cast
  nlinarith

theorem gate_polynomial {n : Nat→Nat} (hn : PolynomiallyBounded n) :
    PolynomiallyBounded (fun q=>normalizedGateDescriptionCap (n q)) := by
  have h1:=polynomiallyBounded_constant 1
  exact polynomiallyBounded_add (polynomiallyBounded_mul
    (polynomiallyBounded_add hn h1)
    (polynomiallyBounded_add (polynomiallyBounded_mul hn hn) h1)) hn

theorem symmetric_description_polynomial {n W : Nat→Nat}
    (hn : PolynomiallyBounded n) (hW : PolynomiallyBounded W) :
    PolynomiallyBounded (fun q=>symmetricDescriptionCap (n q) (W q)) :=
  polynomiallyBounded_mul (polynomiallyBounded_add hW (polynomiallyBounded_constant 1))
    (polynomiallyBounded_add (gate_polynomial hn) (polynomiallyBounded_constant 1))

theorem threshold_description_polynomial {n W : Nat→Nat}
    (hn : PolynomiallyBounded n) (hW : PolynomiallyBounded W) :
    PolynomiallyBounded (fun q=>thresholdDescriptionCap (n q) (W q)) :=
  polynomiallyBounded_add (gate_polynomial hW) (polynomiallyBounded_mul hW (gate_polynomial hn))

theorem restricted_bits (target L : Nat) :
    natBitLength (restrictedParameterBound target (2^L)) ≤ target+L+3 := by
  have hm:=CloseoutNativeWidth.bits_mul_bound ((target+1)*2^L) (target+1) (2^L) le_rfl
  have hp : natBitLength (2^L)=L+1 := by simp [natBitLength,Nat.log_pow]
  have hn : natBitLength (target+1) ≤ target+2 := by
    have h:=Nat.log_le_self 2 (target+1)
    change Nat.log 2 (target+1)+1 ≤ _
    omega
  rw [hp] at hm
  exact hm.trans (by omega)

theorem restricted_gate_polynomial {core target L : Nat→Nat}
    (hc : PolynomiallyBounded core) (ht : PolynomiallyBounded target) (hL : PolynomiallyBounded L) :
    PolynomiallyBounded (fun q=>restrictedGateDescriptionCap (core q) (target q) (2^L q)) := by
  apply polynomiallyBounded_mono
    (larger:=fun q=>(core q+1)*(target q+L q+3)+core q)
  · intro q
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (restricted_bits _ _)) _
  · exact polynomiallyBounded_add (polynomiallyBounded_mul
      (polynomiallyBounded_add hc (polynomiallyBounded_constant 1))
      (polynomiallyBounded_add (polynomiallyBounded_add ht hL) (polynomiallyBounded_constant 3))) hc

theorem restricted_symmetric_polynomial {core target W : Nat→Nat}
    (hc : PolynomiallyBounded core) (ht : PolynomiallyBounded target) (hW : PolynomiallyBounded W) :
    PolynomiallyBounded (fun q=>restrictedSymmetricDescriptionCap (core q) (target q)
      (2^symmetricDescriptionCap (target q) (W q)) (W q)) :=
  polynomiallyBounded_mul (polynomiallyBounded_add hW (polynomiallyBounded_constant 1))
    (polynomiallyBounded_add (restricted_gate_polynomial hc ht
      (symmetric_description_polynomial ht hW)) (polynomiallyBounded_constant 1))

theorem restricted_threshold_polynomial {core target W : Nat→Nat}
    (hc : PolynomiallyBounded core) (ht : PolynomiallyBounded target) (hW : PolynomiallyBounded W) :
    PolynomiallyBounded (fun q=>restrictedThresholdDescriptionCap (core q) (target q)
      (2^thresholdDescriptionCap (target q) (W q)) (thresholdDescriptionCap (target q) (W q))) :=
  polynomiallyBounded_mul
    (polynomiallyBounded_add (threshold_description_polynomial ht hW) (polynomiallyBounded_constant 1))
    (polynomiallyBounded_add (restricted_gate_polynomial hc ht
      (threshold_description_polynomial ht hW)) (polynomiallyBounded_constant 1))

end
end NearCubicWires.RepairSource.CloseoutWitnessResources
