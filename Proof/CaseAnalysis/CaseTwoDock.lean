import Proof.CaseAnalysis.CaseTwoPrepared
import Proof.CaseAnalysis.CaseTwoNativeInput

/-! Match the paid five-input preparation to the existing converter's
literal tape image. All untouched scalar scratch stays outside the focus. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Cold
open LocalBitMultitape RecoveryRootRound RepairRepresentation OuterPCPRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem small_native (j : Fin 74) :
    (∃ k,smallWork k=nativeSlots j) ↔ (j.val≤22 ∨ j=25 ∨ j=28):=by
  fin_cases j <;> decide

theorem prepared_native (hierarchy description address : List Bool) (R B C : ℕ) (A : Fin 135→List Bool)
    (h : Funded hierarchy description address R B C A) (j : Fin 74) :
    prepared R B C description A (nativeSlots j)=nativeInput R B C description j:=by
  simp only [prepared,afterTag,afterDesc,longData,Function.update_apply,smallData,small_native]
  fin_cases j <;> simp [nativeSlots,nativeInput,h.fresh,h.capacity,h.r_width]

theorem converter_dock {R B : ℕ} (c : BooleanCircuit R) (C : ℕ) (hierarchy address : List Bool)
    (A : Fin 135→List Bool)
    (h : Funded hierarchy (frame (canonicalBoundedCircuitDescription B c)) address R B C A) (hC : 1≤C)
    (j : Fin 74) :
    prepared R B C (frame (canonicalBoundedCircuitDescription B c)) A (nativeSlots j)=NativeConverter.framedInput C B c j:=by
  rw [prepared_native hierarchy _ address R B C A h,native_input_eq B C c hC]

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Cold
