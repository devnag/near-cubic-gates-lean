import Proof.CaseAnalysis.WitnessGuardedGcd

/-! The runtime comparison field is exactly the fixed bit policy, truncated
to the actual raw-field width. This handles short and malformed inputs too. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.GcdGuard
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def policyLimit (w bits : ℕ) := 2 ^ min w bits - 1

theorem bits_iff (bits a : ℕ) (hp : 1 ≤ bits) : natBitLength a ≤ bits ↔ a < 2^bits := by
  constructor
  · intro h
    exact (Nat.lt_pow_succ_log_self Nat.one_lt_two a).trans_le
      (Nat.pow_le_pow_right (by decide : 0 < 2) h)
  · intro h
    by_cases hz : a = 0
    · simpa [hz, natBitLength] using hp
    · have hl := Nat.log_lt_of_lt_pow hz h
      unfold natBitLength
      omega

theorem policyLimit_fits (w bits : ℕ) : policyLimit w bits < 2^w := by
  have hp : 0 < 2 ^ min w bits := Nat.two_pow_pos _
  have hle := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.min_le_left w bits)
  unfold policyLimit
  omega

theorem policyLimit_iff (w bits a : ℕ) (hp : 1 ≤ bits) (ha : a < 2^w) :
    a ≤ policyLimit w bits ↔ natBitLength a ≤ bits := by
  rw [bits_iff bits a hp]
  unfold policyLimit
  by_cases hw : w ≤ bits
  · rw [Nat.min_eq_left hw]
    have hle := Nat.pow_le_pow_right (by decide : 0 < 2) hw
    constructor <;> intro _ <;> omega
  · rw [Nat.min_eq_right (by omega : bits ≤ w)]
    have hp : 0 < 2^bits := Nat.two_pow_pos _
    omega

theorem policyLimit_cap (w C : ℕ) (hC : 0 < C) :
    policyLimit w (natBitLength C) < 2*C := by
  apply RationalGuard.bit_cap_numeric C _ hC
  exact (policyLimit_iff w (natBitLength C) _ (by unfold natBitLength; omega)
    (policyLimit_fits w (natBitLength C))).mp (Nat.le_refl _)

theorem policy_run (w a b c C : ℕ) (hC : 0 < C)
    (ha : a < 2^w) (hb : b < 2^w) :
    ∃ r, run machine (8*w+16+(4*C+1)*(32*w+40))
        (bank w a b c (policyLimit w (natBitLength C)) false false) = some r ∧
      r.steps ≤ 8*w+16+(4*C+1)*(32*w+40) ∧ (∀ i, r.final.heads i = 0) ∧
      (readTapeBit (r.final.tapes 8) 0 = true ↔
        natBitLength a ≤ natBitLength C ∧ natBitLength b ≤ natBitLength C) ∧
      (readTapeBit (r.final.tapes 8) 0 = true →
        r.final.tapes 2 = frame (SignedSortKey.binary w (Nat.gcd a b))) := by
  obtain ⟨r, hr, hs, hh, hp, hout⟩ := guarded_run w a b c (policyLimit w (natBitLength C))
    ha hb (policyLimit_fits w (natBitLength C))
  have htime := capped_budget w _ C (policyLimit_cap w C hC)
  have hm := run_moreFuel machine _ (8*w+16+(4*C+1)*(32*w+40)-budget w (policyLimit w (natBitLength C)))
    _ r hr
  rw [Nat.add_sub_of_le htime] at hm
  refine ⟨r, hm, hs.trans htime, hh, ?_, fun h => hout (hp.mp h)⟩
  rw [hp, policyLimit_iff w (natBitLength C) a (by unfold natBitLength; omega) ha,
    policyLimit_iff w (natBitLength C) b (by unfold natBitLength; omega) hb]

end NearCubicWires.RepairOrdinary.CloseoutWitness.GcdGuard
