import Proof.Amplification.RecoveryViewBoot

/-! The materialized100-tape bank is the literal66-tape raw-view input.
The sole shared source slot carries the already advanced witness cursor. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def viewSlots (j : Fin 66) : Fin 100 := if j.val=29 then 23 else ⟨j.val+32,by omega⟩
theorem viewSlots_injective : Function.Injective viewSlots := by decide

theorem boot_native_heads (pos : Nat) :
    (fun j=>bootHeads pos (viewSlots j))=nativeHeads pos := by
  funext j
  fin_cases j <;> rfl

theorem boot_native_tapes (bits word : List Bool) (a : Fin 100→List Bool)
    (ha : Sources bits a) (hs : a 23=frame word) :
    (fun j=>bootTapes bits a (viewSlots j))=nativeTapes bits word := by
  funext j
  fin_cases j <;> simp [viewSlots,bootTapes,bootFlag,falseFlag,trueFlag,nativeTapes,
    stage7,stage6,stage5,stage4,stage3,stage2,stage1,put]
  all_goals first | exact hs | exact ha.empty _ (by decide)

theorem boot_native_layout {s : Nat} (bits word : List Bool) (pos : Nat)
    (a : Fin 100→List Bool) (ha : Sources bits a) (hs : a 23=frame word) (q : Fin s) :
    ZeroPadding.config (nativeCaps bits)
      ⟨q,(fun j=>bootHeads pos (viewSlots j)),(fun j=>bootTapes bits a (viewSlots j))⟩=
      RecoveryRawViewEnd.cfg (view bits word pos) 0 q := by
  rw [boot_native_heads,boot_native_tapes bits word a ha hs]
  exact native_layout bits word pos q

end NearCubicWires.RepairOrdinary.RecoveryColdView
