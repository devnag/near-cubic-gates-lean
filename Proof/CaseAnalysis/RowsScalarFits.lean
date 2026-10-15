import Proof.Hierarchy.CompetitorOffsetScalar

/-! The same scalar field covers the quartic validity test, second moment,
and clause products. Rational normalization can only reduce these integer
bounds. External seeds and threshold children occur in the original
normalizer exactly once. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsScalarFits
open MatrixScoreBatch CompetitorMonomialProducts CompetitorSelectedCount
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def RationalBound (c : ℕ) (a : ℚ) : Prop := a.num.natAbs≤2^c ∧ a.den≤2^c

theorem normalized_product (a b : ℚ) :
    (a*b).num.natAbs≤a.num.natAbs*b.num.natAbs ∧ (a*b).den≤a.den*b.den := by
  have hg : 0<Nat.gcd (a.num*b.num).natAbs (a.den*b.den) :=
    Nat.gcd_pos_of_pos_right _ (Nat.mul_pos a.den_pos b.den_pos)
  have hn := congrArg Int.natAbs (Rat.num_mul_num_eq_num_mul_gcd a b)
  simp only [Int.natAbs_mul,Int.natAbs_natCast] at hn
  simp only [Int.natAbs_mul] at hg
  constructor
  · calc
      (a*b).num.natAbs=(a*b).num.natAbs*1 := (Nat.mul_one _).symm
      _≤(a*b).num.natAbs*Nat.gcd (a.num.natAbs*b.num.natAbs) (a.den*b.den) :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hg)
      _=a.num.natAbs*b.num.natAbs := hn.symm
  · rw [Rat.mul_den]
    exact Nat.div_le_self _ _

theorem rational_product (c d : ℕ) (a b : ℚ)
    (ha : RationalBound c a) (hb : RationalBound d b) : RationalBound (c+d) (a*b) := by
  have hn := (normalized_product a b).1.trans (Nat.mul_le_mul ha.1 hb.1)
  have hd := (normalized_product a b).2.trans (Nat.mul_le_mul ha.2 hb.2)
  simpa only [RationalBound,pow_add] using And.intro hn hd

theorem rational_list (c : ℕ) (xs : List ℚ) (hx : ∀ a∈xs,RationalBound c a) :
    RationalBound (xs.length*c) xs.prod := by
  induction xs with
  | nil => simp [RationalBound]
  | cons a xs ih =>
    have h := rational_product c (xs.length*c) a xs.prod (hx a (by simp))
      (ih (fun b hb => hx b (List.mem_cons_of_mem a hb)))
    simpa only [List.prod_cons,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm] using h

theorem quartic_coefficient (c b : ℕ) (rho : ℚ) (xs : List ℚ)
    (hr : RationalBound 2 rho) (hx : ∀ a∈xs,RationalBound c a)
    (hl : xs.length≤4) (hb : 4*c+2<b) :
    positive (rho*xs.prod)<2^b ∧ negative (rho*xs.prod)<2^b ∧ (rho*xs.prod).den<2^b := by
  have hp := rational_product 2 (xs.length*c) rho xs.prod hr (rational_list c xs hx)
  have hs : 2+xs.length*c<b := by nlinarith
  have hn := hp.1.trans_lt (Nat.pow_lt_pow_right (by decide : 1<2) hs)
  have hd := hp.2.trans_lt (Nat.pow_lt_pow_right (by decide : 1<2) hs)
  have hpos : positive (rho*xs.prod)≤(rho*xs.prod).num.natAbs := by
    unfold positive
    cases (rho*xs.prod).num <;> simp
  have hneg : negative (rho*xs.prod)≤(rho*xs.prod).num.natAbs := by
    unfold negative
    cases (rho*xs.prod).num <;> simp
  exact ⟨hpos.trans_lt hn,hneg.trans_lt hn,hd⟩

theorem normalizer_fits (P h e q b : ℕ) (hP : P<2^h) (hb : h+e+q≤b) :
    P*2^e*2^q<2^b := by
  have hp := Nat.mul_lt_mul_of_pos_right hP (show 0<2^e by positivity)
  have hq := Nat.mul_lt_mul_of_pos_right hp (show 0<2^q by positivity)
  rw [←pow_add,←pow_add] at hq
  exact hq.trans_le (Nat.pow_le_pow_right (by decide) hb)

theorem paper_scalar_width (row : EquationRow.Input) (Q : ℕ) :
    scalarWidth (EquationRow.request row) Q=Q+2*row.d+2*(row.p+1)+4 := by
  rw [scalarWidth,extraWidth_eq]
  change Q+(2*row.d+2*(row.p+1)+4)=_
  omega

theorem quartic_entry_valid (r : Request) (Q c : ℕ) (odd : Bool)
    (f : Fin r.U → Fin r.U → ℕ) (select : Fin r.U → Fin r.U → Bool)
    (rho : ℚ) (xs : List ℚ) (P h e q : ℕ)
    (hf : ∀ i j,f i j<2^Q)
    (hr : RationalBound 2 rho) (hx : ∀ a∈xs,RationalBound c a) (hl : xs.length≤4)
    (hc : 4*c+2<scalarWidth r Q) (hP : P<2^h) (hPpos : 0<P)
    (hd : h+e+q≤ scalarWidth r Q) :
    (CompetitorOffsetScalar.entry odd f select (rho*xs.prod) (P*2^e*2^q)).Valid
      (scalarWidth r Q) := by
  obtain ⟨hp,hn,hden⟩ := quartic_coefficient c _ rho xs hr hx hl hc
  exact CompetitorOffsetScalar.entry_valid r Q odd f select _ _ hf hp hn hden
    (normalizer_fits P h e q _ hP hd) (by positivity)

end NearCubicWires.RepairOrdinary.CloseoutRowsScalarFits
