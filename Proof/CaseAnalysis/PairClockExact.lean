import Proof.Foundations.RecoveryScheduleEnvelope
import Proof.PCP.ProjectionDimensionPolynomial

/-! The exact paper oracle cap can use the existing physical power producer.
Self-pairing plus one is a square, so no separate clock interpreter or cap
enlargement is needed. Compare actual size+1 with this exact positive power. -/
namespace NearCubicWires.RepairSource.CloseoutPairClock
open PolynomialClock RecoveryScheduleEnvelope
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem diagonal_pair_succ (n : Nat) : Nat.pair n n+1=(n+1)^2:=by
  simp only [Nat.pair,lt_self_iff_false,if_false]
  ring

theorem pairIter_succ_exact (depth n : Nat) : pairIter depth n+1=(n+1)^(2^depth):=by
  induction depth generalizing n with
  | zero=>simp [pairIter]
  | succ depth ih=>
    rw [pairIter_succ,ih,diagonal_pair_succ,←pow_mul]
    congr 1
    rw [Nat.pow_succ]
    omega

theorem pairClock_succ_exact (depth n : Nat) : pairClock depth n+1=(n+1)^(2^depth):=
  pairIter_succ_exact depth n

theorem size_guard (G q size : Nat) :
    size≤oracleSizeBound G q ↔ size+1≤(q+1)^(2^(oracleDepth G)):=by
  rw [←pairClock_succ_exact]
  change size≤pairClock (oracleDepth G) q ↔ size+1≤pairClock (oracleDepth G) q+1
  omega

theorem size_guard_produced (G q size : Nat) :
    size≤oracleSizeBound G q ↔
      size+1≤ProjectionNormalization.DimensionPolynomial.value (2^(oracleDepth G)) 1 q:=by
  simpa only [ProjectionNormalization.DimensionPolynomial.value,one_mul] using size_guard G q size

end NearCubicWires.RepairSource.CloseoutPairClock
