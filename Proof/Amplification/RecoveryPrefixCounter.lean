import Proof.Amplification.RecoveryPrefixSentinel

/-! The actual growing binary count update used between prefix queries.
No unary copy of the prefix count is supplied to this incrementer. -/
namespace NearCubicWires.RepairOrdinary.RecoveryPrefixCounter
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem next_bits (n : Nat) : ClockIncrement.next n.bits=(n+1).bits := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit bit n hn ih =>
    rw [Nat.bits_append_bit n bit hn]
    cases bit with
    | false =>
      have he : Nat.bit false n+1=Nat.bit true n := by simp [Nat.bit]
      rw [he,Nat.bits_append_bit n true (by intro _; rfl)]
      rfl
    | true =>
      have he : Nat.bit true n+1=Nat.bit false (n+1) := by simp [Nat.bit]; omega
      rw [he,Nat.bits_append_bit (n+1) false (by omega)]
      exact congrArg (List.cons false) ih

theorem increment_ready (cap n : Nat) (hc : ClockIncrement.work n.bits ≤ cap) :
    ClockJoin.ReadyRun ClockIncrement.machine (4*n.bits.length+8)
      ![ZeroPadding.pad cap (frame n.bits),List.replicate cap false]
      ![ZeroPadding.pad cap (frame (n+1).bits),List.replicate cap false] := by
  obtain ⟨r,hr,hf,hc',hh,hs,_⟩ := ClockIncrement.increment_run n.bits cap
  have hi : ClockJoin.ReadyRun ClockIncrement.machine (2*ClockIncrement.work n.bits+2)
      ![frame n.bits,List.replicate cap false]
      ![frame (n+1).bits,List.replicate cap false] := by
    refine ⟨r,?_,?_,hh,hs.le⟩
    · convert hr using 2
      all_goals first | rfl | (funext i; fin_cases i <;> rfl)
    · funext i
      fin_cases i
      · change r.final.tapes 0=frame (n+1).bits
        simpa only [next_bits] using hf
      · change r.final.tapes 1=List.replicate cap false
        simpa only [max_eq_left hc] using hc'
  have hlarge := ClockJoin.enlarge _ _ _ _ _ hi
    (by have h:=ClockIncrement.work_bound n.bits; omega :
      2*ClockIncrement.work n.bits+2 ≤ 4*n.bits.length+8)
  have padded := PCPPairReusable.padded_ready _ _ _ hlarge (![cap,0] : Fin 2→Nat)
  convert padded using 1
  all_goals funext i; fin_cases i <;> simp

end NearCubicWires.RepairOrdinary.RecoveryPrefixCounter
