import Proof.CaseAnalysis.RowsInteger

/-! Whole all-input cost of the executed canonical integer-list producer.
Its loop count is the actual retained field count, bounded by raw width. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerCold
open CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem loop_budget (bits : List Bool) :
    CloseoutRowsIntegerLoop.budget bits.length (Reencode.fields bits).length≤
      5*coefficient*(bits.length+1)^25+3*(bits.length+1)+3:=by
  have hc:=(CloseoutRowsIntegerList.fields_bound bits).1
  have h:=Nat.mul_le_mul_right (5*CloseoutRowsIntegerReady.capacity bits.length+3) hc
  unfold CloseoutRowsIntegerLoop.budget CloseoutRowsIntegerReady.capacity coefficient at *
  rw [pow_succ (bits.length+1) 24]
  nlinarith

theorem budget_bound (bits : List Bool) : budget bits≤1000000000000000000000000*(bits.length+2)^26:=by
  have hdriver:=InputPower.budget_bound 24 coefficient 1 bits
  have hloop:=loop_budget bits
  have h24:(bits.length+1)^24≤(bits.length+2)^26:=
    (Nat.pow_le_pow_left (by omega) 24).trans (Nat.pow_le_pow_right (by omega) (by decide))
  have h25:(bits.length+1)^25≤(bits.length+2)^26:=
    (Nat.pow_le_pow_left (by omega) 25).trans (Nat.pow_le_pow_right (by omega) (by decide))
  have hdriverPow:(bits.length+1+1)^(24+1)≤(bits.length+2)^26:=by
    rw [show bits.length+1+1=bits.length+2 by omega]
    exact Nat.pow_le_pow_right (by omega) (by decide)
  have hlinear:bits.length+2≤(bits.length+2)^26:=Nat.le_self_pow (by decide) _
  have hpos:1≤(bits.length+2)^26:=Nat.one_le_pow _ _ (by omega)
  unfold budget prepareBudget finishBudget CanonicalTest.budget Reencode.polynomialBudget
    CloseoutRowsIntegerReady.capacity coefficient at *
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerCold
