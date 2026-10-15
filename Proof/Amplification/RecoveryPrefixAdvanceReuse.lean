import Proof.Amplification.RecoveryPrefixAdvance

/-! Sentinel advancement in the physically retained prefix fields and
bounded false workspace used on successive query-loop iterations. -/
namespace NearCubicWires.RepairOrdinary.RecoveryPrefixTail
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem advance_padded (cap : Nat) (xs : List Bool) (answer : Bool)
    (hc : 2*xs.length+13 ≤ cap) :
    ClockJoin.ReadyRun machine (4*xs.length+28)
      ![ZeroPadding.pad cap (frame (xs++[false,true])),ZeroPadding.pad cap [answer],List.replicate cap false]
      ![ZeroPadding.pad cap (frame ((xs++[!answer])++[false,true])),
        ZeroPadding.pad cap [answer],List.replicate cap false] := by
  have base := advance_ready xs answer cap
  rw [max_eq_left hc] at base
  have padded := PCPPairReusable.padded_ready _ _ _ base (![cap,cap,0] : Fin 3→Nat)
  convert padded using 1
  all_goals funext i; fin_cases i <;> simp [List.append_assoc]

end NearCubicWires.RepairOrdinary.RecoveryPrefixTail
