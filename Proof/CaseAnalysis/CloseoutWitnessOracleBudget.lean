import Proof.CaseAnalysis.WitnessOracleRun

/-! The complete cold oracle decoder has one fixed preprocessing polynomial.
The actual source arity is bounded by the actual input length; all malformed
oracle data is charged using the same physical length guard. The degree and
coefficient here are fixed before the hierarchy clock is chosen. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Oracle
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_polynomial (x bits arityBits : List Bool) (hN : 2≤x.length)
    (hcap : 16*bits.length≤x.length) (hq : value arityBits≤x.length) :
    budget x bits arityBits≤40000000000000000000000*(x.length+2)^25:=by
  obtain ⟨hk,_,_⟩:=DAGBounds.guarded_fields x.length bits hN hcap
  have hi:=InputPower.budget_bound 24 coefficient 1 x
  norm_num [coefficient] at hi
  rw [show x.length+1+1=x.length+2 by omega] at hi
  have hl:=DAGBounds.loop_budget (x.length+1) (DAGChecks.words bits).length
    (by omega) (by omega)
  have hh:=DAGHeader.budget_bound (value arityBits) (DAGChecks.words bits).length
  have hs:value arityBits+(DAGChecks.words bits).length+1≤2*(x.length+2):=by omega
  have hs2:=Nat.pow_le_pow_left hs 2
  rw [mul_pow] at hs2
  norm_num only at hs2
  have h2:(x.length+2)^2≤(x.length+2)^25:=
    Nat.pow_le_pow_right (by omega) (by decide)
  have h24:(x.length+1)^24≤(x.length+2)^25:=
    (Nat.pow_le_pow_left (by omega) 24).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  have h25:(x.length+1)^25≤(x.length+2)^25:=Nat.pow_le_pow_left (by omega) 25
  have hf:(bits.length+1)^24≤(x.length+2)^25:=
    (Nat.pow_le_pow_left (by omega) 24).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  have hn:x.length+2≤(x.length+2)^25:=Nat.le_self_pow (by decide) _
  have hp:1≤(x.length+2)^25:=Nat.one_le_pow _ _ (by omega)
  have ho:=payload_bound bits
  unfold budget rawBudget describedBudget compareBudget nodesBudget
    DAGNodes.budget DAGNodes.prefixBudget prepareBudget DAGFields.budget
    NodeReady.capacity NodeScalar.budget coefficient
  omega

end NearCubicWires.RepairOrdinary.CloseoutWitness.Oracle
