import Proof.CaseAnalysis.RowsEstimatorCoefficientsRequest
import Proof.CaseAnalysis.RowsScalarFits

/-! The unreduced operands for the paper's fixed penalty/clause coefficient
and at most four accepted coefficients have exactly the required rational
value and satisfy the same quartic scalar width. No gcd is computed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Fraction
open CloseoutRowsScalarFits
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def signed (negative : Bool) (numerator denominator : ℕ) : CompetitorValidity.Estimate :=
  if negative then ⟨0,numerator,denominator⟩ else ⟨numerator,0,denominator⟩
def parity : List ℚ → Bool
  | [] => false
  | q::qs => Bool.xor (decide (q.num<0)) (parity qs)
def numerator (xs : List ℚ) := (xs.map (fun q => q.num.natAbs)).prod
def denominator (xs : List ℚ) := (xs.map Rat.den).prod
def raw (xs : List ℚ) := signed (parity xs) (numerator xs) (denominator xs)

theorem signed_mul (sa sb : Bool) (a b c d : ℕ) :
    (signed (Bool.xor sa sb) (a*c) (b*d)).value=
      (signed sa a b).value*(signed sb c d).value := by
  cases sa <;> cases sb <;>
    simp [signed,CompetitorValidity.Estimate.value,Bool.xor,Nat.cast_mul,div_mul_div_comm]

theorem signed_rat (q : ℚ) : (signed (decide (q.num<0)) q.num.natAbs q.den).value=q := by
  calc
    _=(q.num : ℚ)/q.den := by
      cases h : q.num with
      | ofNat n => simp [signed,CompetitorValidity.Estimate.value,show ¬(n : ℤ)<0 by omega]
      | negSucc n => simp [signed,CompetitorValidity.Estimate.value,Int.cast_negSucc]
    _=q := Rat.num_div_den q

theorem raw_value (xs : List ℚ) : (raw xs).value=xs.prod := by
  induction xs with
  | nil => simp [raw,parity,numerator,denominator,signed,CompetitorValidity.Estimate.value]
  | cons q xs ih =>
    change (signed (Bool.xor (decide (q.num<0)) (parity xs))
      (q.num.natAbs*numerator xs) (q.den*denominator xs)).value=q*xs.prod
    rw [signed_mul,signed_rat]
    change q*(raw xs).value=q*xs.prod
    rw [ih]

theorem denominator_positive (xs : List ℚ) : 0<denominator xs := by
  induction xs with
  | nil => decide
  | cons q xs ih => exact Nat.mul_pos q.den_pos ih

theorem natural_product_bound (c : ℕ) (f : ℚ → ℕ) (xs : List ℚ)
    (hx : ∀ q∈xs,f q≤2^c) : (xs.map f).prod≤2^(xs.length*c) := by
  induction xs with
  | nil => simp
  | cons q xs ih =>
    have h := Nat.mul_le_mul (hx q (by simp))
      (ih (fun a ha => hx a (List.mem_cons_of_mem q ha)))
    calc
      ((q::xs).map f).prod=f q*(xs.map f).prod := rfl
      _≤2^c*2^(xs.length*c) := h
      _=2^((q::xs).length*c) := by
        rw [List.length_cons,Nat.add_mul,Nat.one_mul,pow_add]
        exact Nat.mul_comm _ _

theorem quartic_bounds (c b : ℕ) (rho : ℚ) (xs : List ℚ)
    (hr : RationalBound 2 rho) (hx : ∀ q∈xs,RationalBound c q)
    (hl : xs.length≤4) (hb : 4*c+2<b) :
    numerator (rho::xs)<2^b ∧ denominator (rho::xs)<2^b := by
  have hn := natural_product_bound c (fun q => q.num.natAbs) xs (fun q hq => (hx q hq).1)
  have hd := natural_product_bound c Rat.den xs (fun q hq => (hx q hq).2)
  have he : 2+xs.length*c<b := by nlinarith
  have hp : 2^(2+xs.length*c)<2^b := Nat.pow_lt_pow_right (by decide) he
  constructor
  · exact (Nat.mul_le_mul hr.1 hn).trans_lt (by simpa only [pow_add] using hp)
  · exact (Nat.mul_le_mul hr.2 hd).trans_lt (by simpa only [pow_add] using hp)

theorem signed_valid (s : Bool) (n d b : ℕ) (hn : n<2^b) (hd : d<2^b) (hp : 0<d) :
    (signed s n d).Valid b := by
  cases s
  · exact ⟨hn,by positivity,hd,hp⟩
  · exact ⟨by positivity,hn,hd,hp⟩

theorem quartic_valid (c b : ℕ) (rho : ℚ) (xs : List ℚ)
    (hr : RationalBound 2 rho) (hx : ∀ q∈xs,RationalBound c q)
    (hl : xs.length≤4) (hb : 4*c+2<b) : (raw (rho::xs)).Valid b := by
  obtain ⟨hn,hd⟩ := quartic_bounds c b rho xs hr hx hl hb
  exact signed_valid _ _ _ b hn hd (denominator_positive _)

theorem quartic_value (rho : ℚ) (xs : List ℚ) : (raw (rho::xs)).value=rho*xs.prod :=
  raw_value (rho::xs)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Fraction
