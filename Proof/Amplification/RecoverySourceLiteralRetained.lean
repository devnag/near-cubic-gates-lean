import Proof.Amplification.RecoverySourceLiteralBudget

/-! The exact literal code run retains its actual address stream for the
other two source literals in the same clause. This is the consumed shared
port contract for the following three-literal machine. -/
namespace NearCubicWires.RepairSource.RecoverySourceLiteralCode
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics SignedSortKey
open VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem retained_code_run (negative : Bool) (skipped : List (List Bool)) (bits suffix : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget negative skipped bits)
      (input (2*skipped.length+negative.toNat).bits (FieldList.stream skipped++RepairOrdinary.frame bits++suffix)) out ∧
      out 44=RepairOrdinary.frame (word negative bits) ∧
      out 11=FieldList.stream skipped++RepairOrdinary.frame bits++suffix := by
  let code := (2*skipped.length+negative.toNat).bits
  let source := FieldList.stream skipped++RepairOrdinary.frame bits++suffix
  obtain ⟨native,hNative,hSign,hAddress,hSource⟩ := RecoverySourceLiteralAddress.address_run negative skipped bits suffix
  have first := hNative.focus nativeSlots native_injective (input code source) (by intro i; fin_cases i <;> rfl)
  have second := (RecoveryLiteralSignFrame.sign_ready negative).focus signSlots sign_injective (addressed code source native) (by
    intro i; fin_cases i
    · change install nativeSlots _ _ (nativeSlots 6)=_
      rw [install_slot _ native_injective]
      exact hSign
    all_goals
      rw [addressed,install_other _ _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl)
  obtain ⟨paired,hPair,hPairField⟩ := PCPPairCold.pair_run [!negative] bits
  have third := hPair.focus pairSlots pair_injective (signed code source native negative)
    (pair_input code source bits native negative hAddress)
  have hall := ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ first second) third
  refine ⟨_,hall,?_,?_⟩
  · change install pairSlots _ _ (pairSlots 26)=_
    rw [install_slot _ pair_injective,hPairField]
    simp only [word,value,Nat.mul_zero,Nat.add_zero]
  · rw [install_other _ _ _ _ (by
      intro i h; have hv:=congrArg Fin.val h
      dsimp only [pairSlots] at hv
      split_ifs at hv <;> dsimp at hv <;> omega)]
    rw [signed,install_other _ _ _ _ (by intro i; fin_cases i <;> decide)]
    change install nativeSlots _ _ (nativeSlots 11)=_
    rw [install_slot _ native_injective]
    exact hSource

end NearCubicWires.RepairSource.RecoverySourceLiteralCode
