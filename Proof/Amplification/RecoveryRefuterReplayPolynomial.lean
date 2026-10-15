import Proof.Amplification.RecoveryRefuterReplay

/-! One fixed polynomial pays the selected refuter request producer,
whole corrected-oracle lift and every composition handoff. -/
namespace NearCubicWires.RepairSource.RecoveryRefuterReplay
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def polynomialCoefficient (code : List Bool) (C D : Nat) := 1125899906842624*(C+D+code.length+1)^6
def polynomialDegree (D : Nat) := 3*(D+2)

theorem budget_bound (code : List Bool) (C D n : Nat) :
    budget code C D n≤polynomialCoefficient code C D*(n+2)^polynomialDegree D := by
  let S := C+D+code.length+1
  let E := (n+2)^(D+2)
  have hs : 1≤S := by dsimp [S]; omega
  have hnE : n+2≤E := by
    calc
      _ = (n+2)^1 := by simp
      _ ≤ E := Nat.pow_le_pow_right (by omega) (by omega)
  have he : 1≤E := by omega
  have hpow : (n+1)^D≤E := by
    exact (Nat.pow_le_pow_left (by omega : n+1≤n+2) D).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hpow' : (n+2)^(D+1)≤E := Nat.pow_le_pow_right (by omega) (by omega)
  have hCE := Nat.mul_le_mul_left C hpow
  have hLE := Nat.mul_le_mul_left (2*code.length) he
  have hsum : C*(n+1)^D+2*code.length+2*n+3≤2*S*E := by
    dsimp [S]
    nlinarith only [hCE,hLE,hnE]
  have hinner : (C*(n+1)^D+2*code.length+2*n+3)^3≤8*S^3*E^3 := by
    calc
      _ ≤ (2*S*E)^3 := Nat.pow_le_pow_left hsum 3
      _ = _ := by ring
  have hs2 : S^2≤S^6 := Nat.pow_le_pow_right hs (by omega)
  have hs3 : S^3≤S^6 := Nat.pow_le_pow_right hs (by omega)
  have he3 : E≤E^3 := by
    calc
      _ = E^1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right he (by omega)
  have hprod : S^2*(n+2)^(D+1)≤S^6*E^3 :=
    Nat.mul_le_mul hs2 (hpow'.trans he3)
  have hinner' : (C*(n+1)^D+2*code.length+2*n+3)^3≤8*(S^6*E^3) := by
    have hh := Nat.mul_le_mul_right (E^3) hs3
    nlinarith only [hinner,hh]
  have hpos : 1≤S^6*E^3 := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul (Nat.one_le_pow 6 S hs) (Nat.one_le_pow 3 E he)
  have heq : E^3=(n+2)^(3*(D+2)) := by dsimp [E]; rw [←pow_mul,Nat.mul_comm (D+2) 3]
  have hlen : (OrdinarySourceSATLift.Request.sourceInput code n).length=2*code.length+2*n+2 := by
    simp only [OrdinarySourceSATLift.Request.sourceInput,List.length_append,frame_length,List.length_replicate]
    omega
  unfold budget OrdinarySourceSATLift.Request.budget polynomialCoefficient polynomialDegree
  rw [hlen]
  change 16*(4096*S^2*(n+2)^(D+1)+1099511627776*(C*(n+1)^D+(2*code.length+2*n+2)+1)^3+1)≤
    1125899906842624*S^6*(n+2)^(3*(D+2))
  rw [←heq]
  have hparen : C*(n+1)^D+(2*code.length+2*n+2)+1=C*(n+1)^D+2*code.length+2*n+3 := by omega
  rw [hparen]
  nlinarith only [hprod,hinner',hpos]

end NearCubicWires.RepairSource.RecoveryRefuterReplay
