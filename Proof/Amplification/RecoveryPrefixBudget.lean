import Proof.Amplification.RecoveryPrefixSentinel

/-! One fixed workspace capacity covers every reachable prefix query and
its two field updates. Its physical production remains a caller operation. -/
namespace NearCubicWires.RepairSource.RecoveryPrefix
open RepairOrdinary RecoveryQuery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workspace (payload limit : Nat) : Nat := 1073741824*(payload.bits.length+2*limit+5)^2

theorem count_width (n : Nat) : n.bits.length ≤ n+1 :=
  (PCPSerializerMass.nat_bits_width n).trans (Nat.add_le_add_right (Nat.log_le_self 2 n) 1)

theorem workspace_covers (payload limit : Nat) (xs : List Bool) (hx : xs.length ≤ limit) :
    capacity payload (commitment xs) (queryCount xs) ≤ workspace payload limit := by
  have hn := count_width (xs.length+1)
  have hl : bytes payload (commitment xs) (queryCount xs)+1 ≤ payload.bits.length+2*limit+5 := by
    simp only [bytes,commitment_length,queryCount]
    omega
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hl 2)

theorem update_capacity (cap payload : Nat) (xs : List Bool)
    (hc : capacity payload (commitment xs) (queryCount xs) ≤ cap) :
    2*xs.length+13 ≤ cap ∧ ClockIncrement.work (queryCount xs).bits ≤ cap ∧
      4*xs.length+4*(queryCount xs).bits.length+41 ≤ 2*cap := by
  have hbase : bytes payload (commitment xs) (queryCount xs)+1 ≤
      (bytes payload (commitment xs) (queryCount xs)+1)^2 := by nlinarith
  have hp : 1 ≤ (bytes payload (commitment xs) (queryCount xs)+1)^2 :=
    Nat.one_le_pow _ _ (by omega)
  have hw := ClockIncrement.work_bound (queryCount xs).bits
  unfold capacity at hc
  simp only [bytes,commitment_length] at hbase hp hc
  omega

end NearCubicWires.RepairSource.RecoveryPrefix
