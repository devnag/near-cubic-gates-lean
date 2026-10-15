import Proof.Amplification.RecoveryValuation

/-! Literal access to the cold-produced zero frame, field width and cap.
These exact tapes, together with the actual witness copy, are wired directly
into the first valuation parse; no repeated allocation is introduced. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdValuation
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem header_width (bits : List Bool) (c s : Nat) :
    RecoveryColdHeader.output bits c s 13=CompareMachine.word (width bits+1) := by
  have h := install_slot RecoveryColdHeader.driverSlots RecoveryColdHeader.driverSlots_injective
    (RecoveryColdHeader.base bits c s (RecoveryColdHeader.fields3 bits))
    (RecoveryEraseDriver.output3 (RecoveryColdHeader.codeWord bits)) (2 : Fin 9)
  change RecoveryColdHeader.output bits c s 13=CompareMachine.word ((RecoveryColdHeader.codeWord bits).length+1) at h
  simpa only [RecoveryColdHeader.code_length,width] using h

theorem header_zero (bits : List Bool) (c s : Nat) :
    RecoveryColdHeader.output bits c s 9=frame (RecoveryColdHeader.zeroWord bits) :=
  install_other RecoveryColdHeader.driverSlots _ _ _ (by intro j; fin_cases j <;> decide)

theorem cap_width (bits : List Bool) (c s : Nat) :
    RecoveryColdHeaderCap.output bits c s 13=CompareMachine.word (width bits+1) := by
  have h := install_other RecoveryColdHeaderCap.slots (RecoveryColdHeaderCap.ambient bits c s)
    ![RecoveryColdCap.word (max 1 bits.length+1+1),RecoveryColdCap.word (RecoveryColdHeaderCap.limit bits),
      List.replicate (3*(max 1 bits.length+1)+3) false] (13 : Fin 22)
    (by intro j; fin_cases j <;> decide)
  exact h.trans (header_width bits c s)

theorem cap_zero (bits : List Bool) (c s : Nat) :
    RecoveryColdHeaderCap.output bits c s 9=frame (RecoveryColdHeader.zeroWord bits) := by
  have h := install_other RecoveryColdHeaderCap.slots (RecoveryColdHeaderCap.ambient bits c s)
    ![RecoveryColdCap.word (max 1 bits.length+1+1),RecoveryColdCap.word (RecoveryColdHeaderCap.limit bits),
      List.replicate (3*(max 1 bits.length+1)+3) false] (9 : Fin 22)
    (by intro j; fin_cases j <;> decide)
  exact h.trans (header_zero bits c s)

theorem cap_cap (bits : List Bool) (c s : Nat) :
    RecoveryColdHeaderCap.output bits c s 20=CompareMachine.word (cap bits) :=
  install_slot RecoveryColdHeaderCap.slots RecoveryColdHeaderCap.slots_injective _ _ 1

theorem preliminary_width (bits word : List Bool) (c s : Nat) :
    RecoveryColdPreliminary.output bits word c s 14=CompareMachine.word (width bits+1) :=
  (RecoveryColdPreliminary.header_retained bits word c s 13).trans (cap_width bits c s)
theorem preliminary_zero (bits word : List Bool) (c s : Nat) :
    RecoveryColdPreliminary.output bits word c s 10=frame (RecoveryColdHeader.zeroWord bits) :=
  (RecoveryColdPreliminary.header_retained bits word c s 9).trans (cap_zero bits c s)
theorem preliminary_cap (bits word : List Bool) (c s : Nat) :
    RecoveryColdPreliminary.output bits word c s 21=CompareMachine.word (cap bits) :=
  (RecoveryColdPreliminary.header_retained bits word c s 20).trans (cap_cap bits c s)
theorem preliminary_word (bits word : List Bool) (c s : Nat) :
    RecoveryColdPreliminary.output bits word c s 23=frame word :=
  RecoveryColdPreliminary.witness_retained bits word c s 1

end NearCubicWires.RepairOrdinary.RecoveryColdValuation
