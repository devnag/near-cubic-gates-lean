import Proof.Amplification.RecoverySATWhole

/-! Uniform budget for the two physically prepared raw banks. Witness
length is charged here and bounded only at canonical NP completeness. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdSAT
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem input_layout (bits word : List Bool) : input bits word=
    fun i : Fin 172=>if i.val=0 then frame bits else if i.val=1 then frame word else [] := by
  funext i
  fin_cases i <;> rfl

theorem bank_bound (bits word : List Bool) :
    bankBudget bits word≤2097152*(bits.length+1)^2+4*word.length+32 := by
  have hb := RecoveryColdView.bank_bound bits
  have hw : width bits≤2*(bits.length+1)+1 := by
    change max 1 bits.length+2≤2*(bits.length+1)+1
    omega
  have hs : bits.length+1≤(bits.length+1)^2 := by
    nlinarith [Nat.zero_le (bits.length*bits.length)]
  unfold bankBudget RecoveryColdView.bankBudget at *
  omega

theorem cold_budget (bits word : List Bool) :
    coldBudget bits word≤268435456*(bits.length+1)^2+12*word.length+256 := by
  have hp := RecoveryColdView.cold_budget bits word
  have hb := bank_bound bits word
  unfold coldBudget
  omega

theorem cold_bounded (bits word : List Bool) :
    ∃ r,run coldProgram (268435456*(bits.length+1)^2+12*word.length+256) (input bits word)=some r ∧
      r.steps≤268435456*(bits.length+1)^2+12*word.length+256 ∧ r.final.heads 30=0 ∧
      r.final.tapes 30=[(readList (limit bits) (readEntry (width bits)) word).isSome] ∧
      ((readList (limit bits) (readEntry (width bits)) word).isSome=true →
        Ready bits word r.final.heads r.final.tapes) := by
  obtain ⟨r,hr,hs,hh,ht,hready⟩ := cold_run bits word
  have hm := run_moreFuel coldProgram (coldBudget bits word)
    (268435456*(bits.length+1)^2+12*word.length+256-coldBudget bits word) _ r hr
  rw [Nat.add_sub_of_le (cold_budget bits word)] at hm
  exact ⟨r,hm,hs.trans (cold_budget bits word),hh,ht,hready⟩

end NearCubicWires.RepairOrdinary.RecoveryColdSAT
