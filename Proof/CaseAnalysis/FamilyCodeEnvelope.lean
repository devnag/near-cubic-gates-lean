import Proof.CaseAnalysis.FamilyCodeBound

open private recoveryWitnessCodeBitBound_parameter_polynomiallyBounded
  from Proof.Amplification.RecoveryWitnessPolicy

/-! One code-size envelope uniform in the oracle and its actual policy.
The constants come from the already checked canonical codec polynomial;
only its numerical argument is bounded, not the accepted witness guard. -/
namespace NearCubicWires.RepairSource.CloseoutFamilyCode
open SourceInterfaces RepairOrdinary CanonicalWitnessCodec RecoveryWitnessPolicy
open PolynomialSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def envelope (coefficient degree parameter V : Nat) :=
  let S:=coefficient*(parameter+1)^degree
  taggedListBitBound [2,S,1+2*V^4*(V*S+1)]

theorem uniform_envelope : ∃ coefficient degree : Nat, 0 < coefficient ∧
    ∀ (limits : RecoveryWitnessLimits) (V parameter : Nat),
      recoveryWitnessCodeParameter limits ≤ parameter →
      bound limits V ≤ envelope coefficient degree parameter V := by
  obtain ⟨C,e,hC,h⟩:=recoveryWitnessCodeBitBound_parameter_polynomiallyBounded
  refine ⟨C,e,hC,?_⟩
  intro limits V parameter hp
  have hS : recoveryWitnessCodeBitBound limits ≤ C*(parameter+1)^e :=
    (h (recoveryWitnessCodeParameter limits)).trans
      (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right hp 1) e))
  unfold bound envelope
  simp only [taggedListBitBound]
  gcongr

theorem envelope_polynomial (coefficient degree : Nat) (parameter V : Nat→Nat)
    (hp : PolynomiallyBounded parameter) (hV : PolynomiallyBounded V) :
    PolynomiallyBounded (fun q=>envelope coefficient degree (parameter q) (V q)) := by
  have h1:=polynomiallyBounded_constant 1
  have h2:=polynomiallyBounded_constant 2
  have h4:=polynomiallyBounded_constant 4
  have hS:=polynomiallyBounded_mul (polynomiallyBounded_constant coefficient)
    (polynomiallyBounded_pow (polynomiallyBounded_add hp h1) degree)
  have hfamily:=polynomiallyBounded_add h1 (polynomiallyBounded_mul
    (polynomiallyBounded_mul h2 (polynomiallyBounded_pow hV 4))
    (polynomiallyBounded_add (polynomiallyBounded_mul hV hS) h1))
  exact polynomiallyBounded_mul h4 (polynomiallyBounded_add h2
    (polynomiallyBounded_mul h4 (polynomiallyBounded_add hS
      (polynomiallyBounded_mul h4 (polynomiallyBounded_add hfamily h1)))))

theorem eventual_sixteenth {f : Nat→Nat} (hf : PolynomiallyBounded f) :
    ∃ onset, ∀ s, onset ≤ s → f s ≤ 2^s/16 := by
  obtain ⟨onset,ho⟩:=polynomiallyBounded_eventually_le_sixteenth_exponential
    (polynomiallyBounded_mul (polynomiallyBounded_constant 2) hf)
  refine ⟨onset,?_⟩
  intro s hs
  have h:=ho s hs
  have hm:=(Nat.le_div_iff_mul_le (by decide : 0 < 16)).mp h
  rw [pow_succ] at hm
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 16)).mpr
  omega

end NearCubicWires.RepairSource.CloseoutFamilyCode
