import Proof.PCP.ProjectionDimensions
import Proof.PCP.ProjectionDimensionPolynomialBounds

/-! Every unary intermediate is bounded by a fixed polynomial in the clock
exponent. The input exponent is unaffected by the later hierarchy degree. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bitLength_le (n : ℕ) : natBitLength n ≤ n+1 := by
  exact Nat.add_le_add_right (Nat.log_le_self 2 n) 1

namespace DimensionWidth

def coefficient (D C : ℕ) := DimensionPolynomial.coefficient D C+16*(C+1)^2+76*(C+1)+47

theorem amount_bound (D C e : ℕ) : amount D C e ≤ (C+1)*(e+2)^(D+1) := by
  have he : e+1 ≤ (e+2)^(D+1) := (by omega : e+1 ≤ e+2).trans
    (Nat.le_self_pow (by omega) _)
  have hp : (e+1)^D ≤ (e+2)^(D+1) :=
    (Nat.pow_le_pow_left (by omega : e+1 ≤ e+2) D).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have ha := Nat.mul_le_mul_left C hp
  have hb := bitLength_le (DimensionPolynomial.value D C e)
  dsimp only [amount,DimensionPolynomial.value] at *
  nlinarith

theorem budget_bound (D C e : ℕ) : budget D C e ≤ coefficient D C*(e+2)^(2*D+2) := by
  let X := (e+2)^(2*D+2)
  have hx : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hp := DimensionPolynomial.budget_bound D C e
  have hr := amount_bound D C e
  have hpow : (e+2)^(D+1) ≤ X := Nat.pow_le_pow_right (by omega) (by omega)
  have hrx : amount D C e ≤ (C+1)*X := hr.trans (Nat.mul_le_mul_left _ hpow)
  have hr2 : (amount D C e)^2 ≤ (C+1)^2*X := by
    have h := Nat.pow_le_pow_left hr 2
    simpa only [mul_pow,←pow_mul,show (D+1)*2=2*D+2 by omega] using h
  have hl : natBitLength (DimensionPolynomial.value D C e) ≤ amount D C e := by dsimp [amount]; omega
  change DimensionPolynomial.budget D C e ≤ DimensionPolynomial.coefficient D C*X at hp
  have hrest : 16*(amount D C e)^2+2*natBitLength (DimensionPolynomial.value D C e)+74*amount D C e+47 ≤
      (16*(C+1)^2+76*(C+1)+47)*X := by nlinarith only [hrx,hr2,hl,hx]
  calc budget D C e = DimensionPolynomial.budget D C e+
      (16*(amount D C e)^2+2*natBitLength (DimensionPolynomial.value D C e)+74*amount D C e+47) := by
        unfold budget; ring
    _ ≤ DimensionPolynomial.coefficient D C*X+(16*(C+1)^2+76*(C+1)+47)*X := Nat.add_le_add hp hrest
    _ = coefficient D C*X := by unfold coefficient; ring
end DimensionWidth

namespace DimensionProducer

def coefficient (p q C : ℕ) := DimensionWidth.coefficient p C+1+
  DimensionPolynomial.coefficient q C*(C+3)^(2*q+2)
def degree (p q : ℕ) := (p+1)*(2*q+2)

theorem budget_bound (p q C e : ℕ) : budget p q C e ≤ coefficient p q C*(e+2)^degree p q := by
  let X := (e+2)^degree p q
  have hx : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hw := DimensionWidth.budget_bound p C e
  have hpoly := DimensionPolynomial.budget_bound q C (DimensionWidth.amount p C e)
  have hwdeg : 2*p+2 ≤ degree p q := by dsimp [degree]; nlinarith
  have hwx := Nat.pow_le_pow_right (by omega : 0<e+2) hwdeg
  have hwidth := hw.trans (Nat.mul_le_mul_left _ hwx)
  have hr := DimensionWidth.amount_bound p C e
  have he1 : 1 ≤ (e+2)^(p+1) := Nat.one_le_pow _ _ (by omega)
  have hr2 : DimensionWidth.amount p C e+2 ≤ (C+3)*(e+2)^(p+1) := by nlinarith
  have hpow := Nat.pow_le_pow_left hr2 (2*q+2)
  have hprod : ((C+3)*(e+2)^(p+1))^(2*q+2)=(C+3)^(2*q+2)*X := by
    rw [mul_pow,←pow_mul]
    rfl
  rw [hprod] at hpow
  have hquery := hpoly.trans (Nat.mul_le_mul_left _ hpow)
  change DimensionWidth.budget p C e ≤ DimensionWidth.coefficient p C*X at hwidth
  calc budget p q C e ≤ DimensionWidth.coefficient p C*X+1+
      DimensionPolynomial.coefficient q C*((C+3)^(2*q+2)*X) :=
        Nat.add_le_add (Nat.add_le_add_right hwidth 1) hquery
    _ ≤ DimensionWidth.coefficient p C*X+X+
      DimensionPolynomial.coefficient q C*((C+3)^(2*q+2)*X) := by omega
    _ = coefficient p q C*X := by unfold coefficient; ring
end DimensionProducer

end NearCubicWires.RepairSource.ProjectionNormalization
