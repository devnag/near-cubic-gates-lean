import Proof.Amplification.RecoveryTseitinTautology

/-! One quadratic capacity covers all original literal triples whose
variable indices have a common binary width. The six physical cells retain
their actual pairing/list operations. Integer screen: 4096 points, seed2506. -/
namespace NearCubicWires.RepairSource.RecoveryTseitin
open RepairOrdinary CanonicalBinary
open private pairSuccBits_le from StatementSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem width_bound (ls : Literals) (W : Nat) (hW : 1 ≤ W)
    (hindex : ∀ j,natBitLength (ls j).2 ≤ W) : width ls ≤ 16*W+7 := by
  have hsign (j : Fin 3) : natBitLength (ls j).1.toNat=1 := by
    generalize (ls j).1=b
    cases b <;> rfl
  have hl (j : Fin 3) : natBitLength (literalCode (ls j)) ≤ 2*W := by
    have h := pairCodeBits_le (ls j).1.toNat (ls j).2
    rw [hsign] at h
    exact h.trans (Nat.mul_le_mul_left 2 (max_le hW (hindex j)))
  have ht : natBitLength (tailOne ls) ≤ 4*W+1 := by
    have h := pairSuccBits_le (literalCode (ls 2)) 0
    change natBitLength (tailOne ls) ≤ 2*max (natBitLength (literalCode (ls 2))) 1+1 at h
    have hm : max (natBitLength (literalCode (ls 2))) 1 ≤ 2*W := max_le (hl 2) (by omega)
    omega
  have hm : natBitLength (tailTwo ls) ≤ 8*W+3 := by
    have h := pairSuccBits_le (literalCode (ls 1)) (tailOne ls)
    change natBitLength (tailTwo ls) ≤ 2*max (natBitLength (literalCode (ls 1))) (natBitLength (tailOne ls))+1 at h
    have hmax : max (natBitLength (literalCode (ls 1))) (natBitLength (tailOne ls)) ≤ 4*W+1 :=
      max_le ((hl 1).trans (by omega)) ht
    omega
  have h := pairSuccBits_le (literalCode (ls 0)) (tailTwo ls)
  have hmax : max (natBitLength (literalCode (ls 0))) (natBitLength (tailTwo ls)) ≤ 8*W+3 :=
    max_le ((hl 0).trans (by omega)) hm
  change width ls ≤ 2*max (natBitLength (literalCode (ls 0))) (natBitLength (tailTwo ls))+1 at h
  omega

theorem capacity_bound (ls : Literals) (W : Nat) (hW : 1 ≤ W)
    (hindex : ∀ j,natBitLength (ls j).2 ≤ W) : capacity ls ≤ 8388608*(W+1)^2 := by
  have hw := width_bound ls W hW hindex
  have hsq : (width ls+1)^2 ≤ (16*(W+1))^2 := Nat.pow_le_pow_left (by omega) 2
  have he : (16*(W+1))^2=256*(W+1)^2 := by ring
  rw [he] at hsq
  have hp : 1 ≤ (W+1)^2 := Nat.one_le_pow _ _ (by omega)
  unfold capacity
  omega

end NearCubicWires.RepairSource.RecoveryTseitin
