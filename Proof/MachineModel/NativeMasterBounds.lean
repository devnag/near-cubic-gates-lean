import Proof.MachineModel.NativeFanoutLayout
import Proof.CaseAnalysis.RowsBankFields

/-! Every distributed metadata word fits the actual measured native C.
The coefficient width, mode width and original arity remain distinct. -/
namespace NearCubicWires.ExtIncidence.NativeMaster
open LocalBitMultitape RepairOrdinary RepairRepresentation
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem words_fit {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ) (i : Fin 15) :
    (words gs Q w i).length ≤ NativeMeasured.capacity gs Q w:=by
  obtain ⟨hc,hi,ho⟩:=CloseoutRowsBankFields.cache_bounds gs (NativeWidth.width gs Q)
    (NativeAllocation.capacity gs Q) Q le_rfl
  have small:=CloseoutRowsPreparationInput.small_fits n (NativeWidth.width gs Q)
    (NativeAllocation.capacity gs Q) w gs.length Q
  unfold CloseoutRowsPreparationBounds.scale at small
  change (words gs Q w i).length ≤ CloseoutRowsPreparationBounds.capacity n
    (NativeWidth.width gs Q) (NativeAllocation.capacity gs Q) w gs.length Q
  have hw : RowCachedCoordinateBounds.width gs ≤
      RowCachedCoordinateBounds.inner (RowCachedCoordinateBounds.width gs):=by
    unfold RowCachedCoordinateBounds.inner;omega
  fin_cases i <;> simp [words,UnaryTemplate.tape,CompareMachine.word,frame_length,SignedSortKey.binary_length]
  all_goals omega

end NearCubicWires.ExtIncidence.NativeMaster
