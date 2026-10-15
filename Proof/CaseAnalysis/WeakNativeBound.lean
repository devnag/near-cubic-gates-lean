import Proof.CaseAnalysis.WeakRuntime
import Proof.Hierarchy.HierarchySourceScales

/-! Discharge the proof-table premise of the actual little-o consumer.
The source proof exponent5+proofLog stays fixed before the hierarchy clock;
only its coefficient depends on that clock. No supplied native width. -/
namespace NearCubicWires.RepairSource.CloseoutWeakRuntime
open RepairOrdinary ProjectionNormalization CloseoutNativeWidth
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def logCoefficient (k C : Nat) := natBitLength C+k+3

theorem clock_log_bound (k C N q : Nat) (hq : 1 ≤ q) (hn : N+1 < 2^q) :
    logScale (C*(N^(k+2)+1)) ≤ logCoefficient k C*q := by
  have hn' : N < 2^q := by omega
  have hp : N^(k+2) < 2^(q*(k+2)) := by
    rw [pow_mul]
    exact Nat.pow_lt_pow_left hn' (by omega)
  have hc : C < 2^natBitLength C := Nat.lt_pow_succ_log_self (by decide) _
  have ht : C*(N^(k+2)+1) < 2^(natBitLength C+q*(k+2)) := calc
    _ ≤ C*2^(q*(k+2)) := Nat.mul_le_mul_left _ (by omega)
    _ < 2^natBitLength C*2^(q*(k+2)) := Nat.mul_lt_mul_of_pos_right hc (by positivity)
    _ = _ := (pow_add _ _ _).symm
  have hl := Nat.log_lt_of_lt_pow' (by unfold natBitLength; omega) ht
  have hshort : natBitLength (C*(N^(k+2)+1)) ≤ natBitLength C+q*(k+2) := by
    change Nat.log 2 (C*(N^(k+2)+1))+1 ≤ natBitLength C+q*(k+2)
    omega
  have hb := (HierarchySourceScales.logScale_le_short (C*(N^(k+2)+1))).trans
    (Nat.add_le_add_right hshort 1)
  have hcoeff : natBitLength C+1 ≤ (natBitLength C+1)*q := by
    simpa only [Nat.mul_one] using (Nat.mul_le_mul_left (natBitLength C+1) hq)
  unfold logCoefficient
  nlinarith

theorem actual_clock_log_bound {v : OrdinaryVerifier}
    (source : ProjectionSourceAlgorithm v UAggregateClock.time) {k : Nat}
    (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad N : Nat) :
    logScale (H.time N) ≤ logCoefficient k H.coefficient*HierarchyProjection.width source H Cpad N := by
  apply clock_log_bound
  · change 1 ≤ Nat.log 2 _+1
    omega
  · exact (input_le_envelope source H Cpad N).trans_lt
      (Nat.lt_pow_succ_log_self (by decide) _)

def tableCoefficient {v : OrdinaryVerifier}
    (source : ProjectionSourceAlgorithm v UAggregateClock.time) {k : Nat}
    (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : Nat) :=
  2*HierarchyProjection.proofCoefficient source H Cpad*H.coefficient*
    (logCoefficient k H.coefficient)^(5+source.degrees.proofLog)

theorem actual_table_bound {v : OrdinaryVerifier}
    (source : ProjectionSourceAlgorithm v UAggregateClock.time) {k : Nat}
    (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : Nat)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (N : Nat) (hn : 1 ≤ N) :
    2^HierarchyProjection.width source H Cpad N ≤
      tableCoefficient source H Cpad*N^(k+2)*
        (HierarchyProjection.width source H Cpad N)^(5+source.degrees.proofLog) := by
  have hp := HierarchyProjection.proof_bound source H Cpad hcoeff hpad N
  have hl := actual_clock_log_bound source H Cpad N
  have ht : H.time N ≤ 2*H.coefficient*N^(k+2) := by
    have hpow : 1 ≤ N^(k+2) := Nat.one_le_pow _ _ hn
    change H.coefficient*(N^(k+2)+1) ≤ _
    nlinarith
  apply hp.trans
  calc
    _ ≤ HierarchyProjection.proofCoefficient source H Cpad*(2*H.coefficient*N^(k+2))*
        (logCoefficient k H.coefficient*HierarchyProjection.width source H Cpad N)^(5+source.degrees.proofLog) := by
      gcongr
    _ = _ := by unfold tableCoefficient; rw [mul_pow]; ring

end NearCubicWires.RepairSource.CloseoutWeakRuntime
