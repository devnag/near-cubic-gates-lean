import Proof.PCP.PCPPRequestNodeDispatch

/-! Paid fixed-depth dispatch has a quadratic bound in its three encoded
operand widths; it does not expand a represented number to unary. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeDispatch
open LocalBitMultitape PCPPRequestNodeCode
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_quadratic (a b c : ℕ) (flag : Bool) :
    budget a b c flag ≤ 4294967296*(a.bits.length+b.bits.length+c.bits.length+1)^2 := by
  let m := a.bits.length+b.bits.length+c.bits.length+1
  let tail := if flag then Nat.pair 1 (Nat.pair c 0) else 0
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hab : a.bits.length ≤ m ∧ b.bits.length ≤ m ∧ c.bits.length ≤ m := by dsimp [m]; omega
  have ht : tail.bits.length ≤ 8*m := by
    cases flag
    · change 0 ≤ 8*m; omega
    · exact (PCPPRequestTaggedCons.cons_bits c 0).trans (by change 8*(c.bits.length+0+1) ≤ 8*m; dsimp [m]; omega)
  have hmid : (middle b c flag).bits.length ≤ 80*m := by
    have h := PCPPRequestTaggedCons.cons_bits b tail
    change (middle b c flag).bits.length ≤ 8*(b.bits.length+tail.bits.length+1) at h
    omega
  have bounded (x y : ℕ) (h : x.bits.length+y.bits.length+1 ≤ 82*m) :
      PCPPRequestTaggedCons.budget x y ≤ 500000000*m^2 := by
    calc
      _  ≤  65536*(x.bits.length+y.bits.length+1)^2 := PCPPRequestTaggedCons.budget_quadratic x y
      _  ≤  65536*(82*m)^2 := by gcongr
      _  ≤  500000000*m^2 := by ring_nf; omega
  have ha := bounded a (middle b c flag) (by omega)
  have hb := bounded b tail (by omega)
  have hc := bounded c 0 (by change c.bits.length+0+1 ≤ 82*m; omega)
  have hpow : 1 ≤ m^2 := Nat.one_le_pow 2 _ hm
  change budget a b c flag ≤ 4294967296*m^2
  cases flag
  · change 4+1+PCPPRequestTaggedCons.budget b 0+1+
      PCPPRequestTaggedCons.budget a (middle b 0 false)+2 ≤ 4294967296*m^2
    change PCPPRequestTaggedCons.budget b 0 ≤ 500000000*m^2 at hb
    change PCPPRequestTaggedCons.budget a (middle b 0 false) ≤ 500000000*m^2 at ha
    omega
  · change 4+1+PCPPRequestTaggedCons.budget c 0+1+
      PCPPRequestTaggedCons.budget b (Nat.pair 1 (Nat.pair c 0))+1+
      PCPPRequestTaggedCons.budget a (middle b c true)+2 ≤ 4294967296*m^2
    change PCPPRequestTaggedCons.budget b (Nat.pair 1 (Nat.pair c 0)) ≤ 500000000*m^2 at hb
    omega

end NearCubicWires.RepairOrdinary.PCPPRequestNodeDispatch
