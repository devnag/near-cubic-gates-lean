import Proof.CaseAnalysis.CaseTwoAddressFields
import Proof.Amplification.RecoveryTseitinReadOnly

/-! The actual arity tape survives both occurrence-field readers. This is
rule-table preservation of the already paid tape, with no extra producer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.AddressRetention
open LocalBitMultitape RepairSource RecoveryTseitinReadOnly ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem record_readonly {t s : ℕ} (p : Machine t s) (target i : Fin t) (hp : NoWrite p i) :
    NoWrite (AppendOutputLength.record p target) (i.castAdd 1):=by
  intro state
  refine Fin.addCases (fun q bits a ha=>?_) (fun q bits a ha=>?_) state
  · by_cases hh : p.halted q=true
    · simp [AppendOutputLength.record,CursorRestore.machine,hh] at ha
      subst a
      simp [Rewind.bridgeAction]
    · cases hr : p.rule q (fun j=>bits (j.castAdd 1)) with
      | none => simp [AppendOutputLength.record,CursorRestore.machine,hh,hr] at ha
      | some b =>
        simp [AppendOutputLength.record,CursorRestore.machine,hh,hr] at ha
        subst a
        simpa only [CursorRestore.recordAction,Fin.addCases_left] using hp q (fun j=>bits (j.castAdd 1)) b hr
  · simp only [AppendOutputLength.record,CursorRestore.machine,Fin.addCases_right] at ha
    split at ha
    · split at ha
      · cases ha;simp [MaskedReset.rewindAction]
      · cases ha;simp [Rewind.finishAction]
    · contradiction

theorem frame_readonly {t s : ℕ} (p : Machine t s) (target i : Fin t)
    (hi : i≠target) (hp : NoWrite p i) :
    NoWrite (AppendOutputFrame.machine p target) (PCPPNativeFrame.old i):=by
  apply composition
  · exact embedded 2 _ _ (rewind _ _ (record_readonly p target i hp))
  · exact unselected (AppendOutputFrame.slots target) _ _ (PCPPNativeFrame.old_away target i hi)

theorem slice_driver (i : Fin 4) (hi : i=2 ∨ i=3) :
    NoWrite SliceFrame.machine (PCPPNativeFrame.old i):=by
  apply frame_readonly VerifierDecoding.SliceMachine.machine 1 i (by rcases hi with rfl|rfl <;>decide)
  intro q bits a ha
  simp only [VerifierDecoding.SliceMachine.machine] at ha
  split_ifs at ha <;>cases ha <;>
    rcases hi with rfl|rfl <;>rfl

theorem binary_offset : NoWrite BinaryField.machine 2:=by
  apply composition
  · exact focus BinaryField.sliceSlots BinaryField.slice_injective SliceFrame.machine 2
      (slice_driver 2 (Or.inl rfl))
  · exact unselected BinaryField.countSlots _ _ (by decide)

theorem arity_readonly : NoWrite AddressFields.machine 1:=by
  apply composition
  · apply composition
    · apply composition
      · exact unselected AddressFields.oneSlots _ _ (by decide)
      · exact focus AddressFields.inputSlots (by decide) SliceFrame.machine 3
          (slice_driver 3 (Or.inr rfl))
    · exact focus AddressFields.clauseSlots (by decide) BinaryField.machine 2 binary_offset
  · exact unselected AddressFields.positionSlots _ _ (by decide)

theorem arity_retained {q cb : ℕ} (u : BitInput q) (clause : BitInput cb)
    (pad : List Bool) (position : Bool) (fuel : ℕ) (out : ExecutionReceipt 27 _)
    (hr : run AddressFields.machine fuel (AddressFields.input u clause pad position)=some out) :
    out.final.tapes 1=List.replicate q true:=
  run_tape AddressFields.machine 1 arity_readonly fuel _ out hr

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.AddressRetention
