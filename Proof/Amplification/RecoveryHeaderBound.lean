import Proof.Amplification.RecoveryHeaderTail

/-! Uniform quadratic bound for the entire cold scalar-header producer,
including exact padded code/bound/zero frames and the actual erase driver. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdHeader
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem width_le (bits : List Bool) : width bits ≤ bits.length+3 := by
  unfold width RecoveryColdWidth.width
  omega

theorem budget_le (bits : List Bool) : budget bits ≤ 16777216*(bits.length+1)^2 := by
  have hc := RecoveryColdDimensions.budget_le bits
  have hw := width_le bits
  have hd := RecoveryEraseDriver.time_bound (codeWord bits)
  simp only [RecoveryEraseDriver.budget,RecoveryEraseDriver.coefficient,codeWord,
    RecoveryColdPaddedCopy.data_length] at hd
  change RecoveryEraseDriver.time (codeWord bits) ≤ 64*(8192+1)*(width bits+1)^2 at hd
  have hs : (width bits+1)^2 ≤ 16*(bits.length+1)^2 := by nlinarith only [hw]
  unfold budget tailTime
  nlinarith only [hc,hd,hw,hs]

theorem code_length (bits : List Bool) : (codeWord bits).length=width bits :=
  RecoveryColdPaddedCopy.data_length _ _
theorem bound_length (bits : List Bool) : (boundWord bits).length=width bits :=
  RecoveryColdPaddedCopy.data_length _ _
theorem zero_length (bits : List Bool) : (zeroWord bits).length=width bits :=
  RecoveryColdPaddedCopy.data_length _ _

theorem code_value (bits : List Bool) : RadixSemantics.value (codeWord bits)=RadixSemantics.value bits := by
  apply RecoveryColdPaddedCopy.data_value
  unfold width RecoveryColdWidth.width
  omega

theorem bound_value (bits : List Bool) : RadixSemantics.value (boundWord bits)=max 1 bits.length := by
  have hb : (bound bits).length ≤ width bits := by
    apply ClockBinary.length_bound
    have hn : max 1 bits.length < 2^(max 1 bits.length) := Nat.lt_two_pow_self
    have he : 2^(max 1 bits.length) ≤ 2^(width bits) := by
      apply Nat.pow_le_pow_right (by decide)
      unfold width RecoveryColdWidth.width
      omega
    exact hn.trans_le he
  change RadixSemantics.value (RecoveryColdPaddedCopy.data (bound bits) (width bits))=max 1 bits.length
  rw [RecoveryColdPaddedCopy.data_value _ _ hb]
  exact ClockBinary.word_value _

theorem zero_value (bits : List Bool) : RadixSemantics.value (zeroWord bits)=0 := by
  have h := RecoveryColdPaddedCopy.data_value [] (width bits) (Nat.zero_le _)
  exact h

theorem header_bounded (bits : List Bool) :
    ∃ cap scratch,cap ≤ 2*PCPResourceLedger.ell bits.length+3 ∧ scratch ≤ HierarchyInputLength.rawBudget bits ∧
      ∃ r,run machine (16777216*(bits.length+1)^2) (input bits)=some r ∧
        r.final.heads=(fun _=>0) ∧ r.final.tapes=output bits cap scratch ∧
        r.steps ≤ 16777216*(bits.length+1)^2 := by
  obtain ⟨cap,scratch,hcap,hscratch,r,hr,hh,ht,hs⟩ := header_run bits
  have h := run_moreFuel machine (budget bits) (16777216*(bits.length+1)^2-budget bits) _ r hr
  rw [Nat.add_sub_of_le (budget_le bits)] at h
  exact ⟨cap,scratch,hcap,hscratch,r,h,hh,ht,hs.trans (budget_le bits)⟩

end NearCubicWires.RepairOrdinary.RecoveryColdHeader
