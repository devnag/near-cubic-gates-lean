import Proof.Amplification.RecoveryViewWhole

/-! Uniform cold raw-view allocation bound, including the full retained
witness copy. Only canonical completeness will bound witness length by B. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem input_layout (bits word : List Bool) : input bits word=
    fun i : Fin 100=>if i.val=0 then frame bits else if i.val=1 then frame word else [] := by
  funext i
  fin_cases i <;> rfl

theorem cold_budget (bits word : List Bool) :
    coldBudget bits word≤134217728*(bits.length+1)^2+8*word.length+128 := by
  have hp := RecoveryColdValuation.cold_budget bits word
  have hb := bank_bound bits
  unfold coldBudget RecoveryColdValuation.resumedBudget
  nlinarith only [hp,hb]

theorem cold_bounded (bits word : List Bool) :
    ∃ r,run coldProgram (134217728*(bits.length+1)^2+8*word.length+128) (input bits word)=some r ∧
      r.steps≤134217728*(bits.length+1)^2+8*word.length+128 ∧ r.final.heads 30=0 ∧
      r.final.tapes 30=[(readList (limit bits) (readEntry (width bits)) word).isSome] ∧
      ((readList (limit bits) (readEntry (width bits)) word).isSome=true →
        Ready bits word r.final.heads r.final.tapes) := by
  obtain ⟨r,hr,hs,hh,ht,hready⟩ := cold_run bits word
  have h := run_moreFuel coldProgram (coldBudget bits word)
    (134217728*(bits.length+1)^2+8*word.length+128-coldBudget bits word) _ r hr
  rw [Nat.add_sub_of_le (cold_budget bits word)] at h
  exact ⟨r,h,hs.trans (cold_budget bits word),hh,ht,hready⟩

end NearCubicWires.RepairOrdinary.RecoveryColdView
