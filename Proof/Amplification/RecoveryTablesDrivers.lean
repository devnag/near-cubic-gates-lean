import Proof.Amplification.RecoveryTablesOutput

/-! The table materializer's width and cap drivers are already physically
present in the retained final raw-view bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ready_drivers (bits word : List Bool) (h : Fin 100→Nat) (a : Fin 100→List Bool)
    (hr : Ready bits word h a) :
    h 62=1 ∧ a 62=CompareMachine.word (2*width bits) ∧
      h 96=1 ∧ a 96=CompareMachine.word (limit bits) := by
  obtain ⟨_,_,count,b,_,_,_,hb,hs,_,hh,ht⟩ := hr
  have hm := boot_native_tapes bits word b hb hs
  refine ⟨by rw [hh]; rfl,?_,by rw [hh]; rfl,?_⟩
  · rw [ht]
    exact congrFun hm (30 : Fin 66)
  · rw [ht]
    exact congrFun hm (64 : Fin 66)

end NearCubicWires.RepairOrdinary.RecoveryColdView

namespace NearCubicWires.RepairOrdinary.RecoveryColdSAT
open RepairSource.VerifierDecoding
theorem ready_drivers (bits word : List Bool) (h : Fin 172→Nat) (a : Fin 172→List Bool)
    (hr : Ready bits word h a) :
    h 62=1 ∧ a 62=CompareMachine.word (2*RecoveryColdView.width bits) ∧
      h 96=1 ∧ a 96=CompareMachine.word (RecoveryColdView.limit bits) :=
  RecoveryColdView.ready_drivers bits word _ _ (ready_view bits word h a hr)

end NearCubicWires.RepairOrdinary.RecoveryColdSAT
