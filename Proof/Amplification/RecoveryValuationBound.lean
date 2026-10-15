import Proof.Amplification.RecoveryValuationWhole

/-! Uniform bound for the whole cold valuation gate and its literal parse
meaning. The finite numeric screen is recorded in cold-valuation-smoke1;
the bound below is a universal Lean theorem. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdValuation
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem parser_budget (bits : List Bool) :
    RecoveryValuationCount.limit (width bits) (cap bits)≤512*(bits.length+1)^2 := by
  have hb : max 1 bits.length≤bits.length+1 := by omega
  have hs := Nat.pow_le_pow_left hb 2
  unfold RecoveryValuationCount.limit RecoveryValuationStream.budget cap RecoveryColdHeaderCap.limit
    width RecoveryColdHeader.width RecoveryColdWidth.width
  nlinarith only [hb,hs]

theorem cold_budget (bits word : List Bool) :
    coldBudget bits word≤67108864*(bits.length+1)^2+8*word.length+64 := by
  have hp := RecoveryColdPreliminary.budget_le bits word
  have hv := parser_budget bits
  unfold coldBudget
  nlinarith only [hp,hv]

theorem cold_bounded (bits word : List Bool) :
    ∃ r,run coldMachine (67108864*(bits.length+1)^2+8*word.length+64) (input bits word)=some r ∧
      r.steps≤67108864*(bits.length+1)^2+8*word.length+64 ∧ r.final.heads 30=0 ∧
      r.final.tapes 30=[(readList (cap bits) (readEntry (width bits)) word).isSome] := by
  obtain ⟨r,hr,hs,hh,ht⟩ := cold_run bits word
  have h := run_moreFuel coldMachine (coldBudget bits word)
    (67108864*(bits.length+1)^2+8*word.length+64-coldBudget bits word) _ r hr
  rw [Nat.add_sub_of_le (cold_budget bits word)] at h
  exact ⟨r,h,hs.trans (cold_budget bits word),hh,ht⟩

end NearCubicWires.RepairOrdinary.RecoveryColdValuation
