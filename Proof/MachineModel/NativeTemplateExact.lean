import Proof.MachineModel.NativeTemplateTail
import Proof.MachineModel.NativeMasterBounds

/-! Observed bits and the proved common extent identify the exact native
input lists, so false backing never becomes a prepared-word assumption. -/
namespace NearCubicWires.ExtIncidence.NativeTemplate
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryBoundedTapeCopy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem exact_input {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ)
    (out : List Bool) (i : Fin 113)
    (h31 : i≠31) (h52 : i≠52) (h104 : i≠104) (h105 : i≠105) (h107 : i≠107) :
    let C:=NativeMeasured.capacity gs Q w
    (CloseoutRowsBankPolynomial.entry gs (NativeWidth.width gs Q)
      (NativeAllocation.capacity gs Q) Q w C [] out).tapes i=
        ZeroPadding.pad C (payload gs Q w i):=by
  dsimp only
  let C:=NativeMeasured.capacity gs Q w
  let E:=(CloseoutRowsBankPolynomial.entry gs (NativeWidth.width gs Q)
    (NativeAllocation.capacity gs Q) Q w C [] out).tapes i
  have size : E.length ≤ C:=BankOptional.entry_size gs (NativeWidth.width gs Q)
    (NativeAllocation.capacity gs Q) Q w [] out (by simp) (by simp) le_rfl i h31 h105
  have len : E.length=C:=by
    apply Nat.le_antisymm size
    change C ≤ (ZeroPadding.pad (CloseoutRowsBankCapacity.capacities C i) _).length
    rw [ZeroPadding.pad_length]
    simp only [CloseoutRowsBankCapacity.capacities,h31,h105,↓reduceIte]
    exact Nat.le_max_left _ _
  have fit : (payload gs Q w i).length ≤ C:=by
    unfold payload NativeFanout.word
    cases h : select i with
    | none => simp
    | some j => exact NativeMaster.words_fit gs Q w j
  have bits : readTapeBit E=readTapeBit (payload gs Q w i):=by
    funext pos;exact reads gs Q w C out i pos h31 h52 h104 h105 h107
  have same : RecoveryBoundedTapeCopy.copied E C=E:=by
    simpa only [len] using CloseoutRowsMetadataCopy.copied_self E
  change E=ZeroPadding.pad C (payload gs Q w i)
  rw [←same]
  have copied_same : RecoveryBoundedTapeCopy.copied E C=RecoveryBoundedTapeCopy.copied (payload gs Q w i) C:=by simp only [RecoveryBoundedTapeCopy.copied,bits]
  rw [copied_same]
  exact CloseoutRowsMetadataCopy.copied_pad _ C fit

end NearCubicWires.ExtIncidence.NativeTemplate
