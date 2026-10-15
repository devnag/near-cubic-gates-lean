import Proof.Amplification.RecoveryViewBootLayout

/-! Seven physical copies followed by the paid native-reader boot.
The gate bit and original certificate/count data remain available. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def preparedProgram := Composition.machine bankProgram bootProgram
theorem prepared_run (bits : List Bool) (pos : Nat) (a : Fin 100→List Bool) (ha : Sources bits a) :
    ∃ r,runFrom preparedProgram (bankBudget bits+2) ⟨preparedProgram.start,bankHeads pos,a⟩=some r ∧
      r.final.heads=bootHeads pos ∧ r.final.tapes=bootTapes bits a := by
  obtain ⟨first,hfirst,hfh,hft,_⟩ := bank_run bits pos a ha
  obtain ⟨last,hlast,hlh,hlt⟩ := boot_run bits pos a ha
  have hi : Composition.restart first.final bootProgram.start=
      (⟨bootProgram.start,bankHeads pos,stage7 bits a⟩ : Configuration 100 2) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  rw [←hi] at hlast
  have h := Composition.run_join bankProgram bootProgram (bankBudget bits) 1 _ first last hfirst hlast
  rw [show bankBudget bits+1+1=bankBudget bits+2 by omega] at h
  exact ⟨Composition.joinedReceipt first last,h,hlh,hlt⟩

theorem boot_retained (bits : List Bool) (a : Fin 100→List Bool) :
    bootTapes bits a 23=a 23 ∧ bootTapes bits a 30=a 30 ∧ bootTapes bits a 31=a 31 := by
  simp [bootTapes,bootFlag,falseFlag,trueFlag,stage7,stage6,stage5,stage4,stage3,stage2,stage1,put]

theorem initial_reject {t s u : Nat} (p : Machine t s) (q : Machine t u) (slot : Fin t)
    (fuel : Nat) (input : Fin t→List Bool) (first : ExecutionReceipt t s)
    (hr : run p fuel input=some first) (hh : first.final.heads slot=0)
    (ht : first.final.tapes slot=[false]) :
    ∃ r,run (RecoveryGatedSequence.machine p q slot) (fuel+1) input=some r ∧
      r.steps≤fuel+1 ∧ r.final.heads=first.final.heads ∧ r.final.tapes=first.final.tapes := by
  obtain ⟨r,h,hs,hf⟩ := RecoveryGatedSequence.reject_run p q slot fuel _ first hr hh ht
  exact ⟨r,h,hs,by rw [hf]; rfl,by rw [hf]; rfl⟩

theorem initial_accept {t s u : Nat} (p : Machine t s) (q : Machine t u) (slot : Fin t)
    (b1 b2 : Nat) (input : Fin t→List Bool) (first : ExecutionReceipt t s) (last : ExecutionReceipt t u)
    (hr : run p b1 input=some first) (hh : first.final.heads slot=0)
    (ht : first.final.tapes slot=[true])
    (hl : runFrom q b2 (RecoveryCalls.restarted q first.final.heads first.final.tapes)=some last) :
    ∃ r,run (RecoveryGatedSequence.machine p q slot) (b1+b2+2) input=some r ∧
      r.steps≤b1+b2+2 ∧ r.final.heads=last.final.heads ∧ r.final.tapes=last.final.tapes := by
  obtain ⟨r,h,hs,hf⟩ := RecoveryGatedSequence.accept_run p q slot b1 b2 _ first last hr hh ht hl
  exact ⟨r,h,hs,by rw [hf]; rfl,by rw [hf]; rfl⟩

end NearCubicWires.RepairOrdinary.RecoveryColdView
