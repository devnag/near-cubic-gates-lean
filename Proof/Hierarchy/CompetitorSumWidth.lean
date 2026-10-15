import Proof.Hierarchy.CompetitorReusableSum

/-! A single polynomial scalar width for every prefix of the literal signed
rational fold. Multiplication is performed at local width 2B+2; the crop to
B is exact because this theorem bounds every semantic prefix denominator. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSumWidth
open CompetitorValidity CompetitorRationalNumerators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def zero : Estimate := ⟨0,0,1⟩
def width (n k : ℕ) := (n+1)*(k+1)
structure PrefixBound (R n : ℕ) (a : Estimate) : Prop where
  positive : a.positive≤n*R^n
  negative : a.negative≤n*R^n
  denominator : a.denominator≤R^n
  denominatorPositive : 0<a.denominator
def Trace (b : ℕ) : Estimate → List Estimate → Prop
  | a,[] => a.Valid b
  | a,c::cs => a.Valid b ∧ c.Valid b ∧ Trace b (add a c) cs

theorem step_bound (R n : ℕ) (a c : Estimate) (ha : PrefixBound R n a)
    (hp : c.positive≤R) (hn : c.negative≤R) (hd : c.denominator≤R) (hpos : 0<c.denominator) :
    PrefixBound R (n+1) (add a c) := by
  constructor
  · change a.positive*c.denominator+c.positive*a.denominator≤_
    calc
      _ ≤ (n*R^n)*R+R*R^n := Nat.add_le_add (Nat.mul_le_mul ha.positive hd)
        (Nat.mul_le_mul hp ha.denominator)
      _ = (n+1)*R^(n+1) := by rw [pow_succ]; ring
  · change a.negative*c.denominator+c.negative*a.denominator≤_
    calc
      _ ≤ (n*R^n)*R+R*R^n := Nat.add_le_add (Nat.mul_le_mul ha.negative hd)
        (Nat.mul_le_mul hn ha.denominator)
      _ = (n+1)*R^(n+1) := by rw [pow_succ]; ring
  · change a.denominator*c.denominator≤_
    simpa only [pow_succ] using Nat.mul_le_mul ha.denominator hd
  · exact Nat.mul_pos ha.denominatorPositive hpos

theorem exponent_bound (n k j : ℕ) (hj : j≤n) :
    j*(2^k)^j<2^width n k ∧ (2^k)^j<2^width n k := by
  have hp' : 0<((2 : ℕ)^k)^j := by positivity
  have hjpow : j<2^j := Nat.lt_two_pow_self
  have hexp : j+k*j<width n k := by unfold width; nlinarith
  have hexp' : k*j<width n k := by omega
  constructor
  · calc
      j*(2^k)^j < 2^j*(2^k)^j := Nat.mul_lt_mul_of_pos_right hjpow hp'
      _ = 2^(j+k*j) := by rw [← pow_mul,← pow_add]
      _ < 2^width n k := Nat.pow_lt_pow_right (by decide) hexp
  · rw [← pow_mul]
    exact Nat.pow_lt_pow_right (by decide) hexp'

theorem bound_valid (n k j : ℕ) (hj : j≤n) (a : Estimate)
    (ha : PrefixBound (2^k) j a) : a.Valid (width n k) := by
  have hh := exponent_bound n k j hj
  exact ⟨ha.positive.trans_lt hh.1,ha.negative.trans_lt hh.1,
    ha.denominator.trans_lt hh.2,ha.denominatorPositive⟩

theorem input_valid (n k : ℕ) (a : Estimate) (ha : a.Valid k) : a.Valid (width n k) := by
  have hkw : k≤width n k := by unfold width; nlinarith
  have hp : 2^k≤2^width n k := Nat.pow_le_pow_right (by decide) hkw
  exact ⟨ha.positive.trans_le hp,ha.negative.trans_le hp,ha.denominator.trans_le hp,ha.denominatorPositive⟩

theorem trace_from_bound (n k j : ℕ) (a : Estimate) (xs : List Estimate)
    (hlen : j+xs.length≤n) (ha : PrefixBound (2^k) j a)
    (hxs : ∀ c∈xs,c.Valid k) : Trace (width n k) a xs := by
  induction xs generalizing j a with
  | nil => exact bound_valid n k j (by simpa using hlen) a ha
  | cons c cs ih =>
    have hc := hxs c (by simp)
    refine ⟨bound_valid n k j (by simp only [List.length_cons] at hlen; omega) a ha,
      input_valid n k c hc,?_⟩
    apply ih (j+1) (add a c) (by simp only [List.length_cons] at hlen; omega)
      (step_bound (2^k) j a c ha hc.positive.le hc.negative.le hc.denominator.le hc.denominatorPositive)
    intro d hd
    exact hxs d (by simp [hd])

theorem uniform_trace (k : ℕ) (xs : List Estimate) (hxs : ∀ c∈xs,c.Valid k) :
    Trace (width xs.length k) zero xs := by
  apply trace_from_bound xs.length k 0 zero xs (by omega) _ hxs
  constructor <;> simp [zero]

end NearCubicWires.RepairOrdinary.CompetitorSumWidth
