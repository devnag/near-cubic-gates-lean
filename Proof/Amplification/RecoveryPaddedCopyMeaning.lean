import Proof.Amplification.RecoveryPaddedCopyWhole

/-! Padding the executed field preserves its value whenever the actual
produced width contains the source. No canonical reencoding is required. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdPaddedCopy
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem data_eq_pad (bits : List Bool) (width : Nat) (hw : bits.length≤width) :
    data bits width=bits++List.replicate (width-bits.length) false := by
  apply List.ext_getElem
  · simp only [data_length,List.length_append,List.length_replicate]
    omega
  · intro i hi hj
    simp only [data,List.getElem_map,List.getElem_range]
    by_cases hib : i<bits.length
    · rw [List.getElem_append_left hib]
      simp [readTapeBit,List.getD,hib]
    · rw [List.getElem_append_right (by omega)]
      simp [readTapeBit,List.getD,hib]

theorem data_value (bits : List Bool) (width : Nat) (hw : bits.length≤width) :
    RadixSemantics.value (data bits width)=RadixSemantics.value bits := by
  rw [data_eq_pad bits width hw,RadixSemantics.value_append,RecoveryRootIteration.zeros_value]
  omega

end NearCubicWires.RepairOrdinary.RecoveryColdPaddedCopy
