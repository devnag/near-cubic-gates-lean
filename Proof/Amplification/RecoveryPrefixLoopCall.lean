import Proof.Amplification.RecoveryPrefixPrepareCall

/-! The complete actual oracle prefix search on the physically constructed
wide state. The same native payload and driver determine all prefix queries. -/
namespace NearCubicWires.RepairSource.RecoveryPrefixCold
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open RecoveryPrefixBody
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Searched (cap total : Nat) (xs : List Bool) (ambient : Fin 389→List Bool) : Prop :=
  ambient 2=ZeroPadding.pad cap (frame (xs++[false,true])) ∧
  ambient 361=VerifierDecoding.CompareMachine.word total ∧
  ∀ i : Fin 389,382 ≤ i.val → ambient i=[]

theorem loop_input (flat : Bool) (C payload total : Nat) (ambient : Fin 389→List Bool)
    (hi : Prepared C payload total ambient) :
    ∀ i : Fin 361,ambient (loopSlots i)=
      RecoveryPrefixLoopDock.tapes (RecoveryPrefixBody.program flat) total (ambient ∘ nativeSlot) i := by
  intro i
  refine Fin.addCases (m:=360) (n:=1) (fun j=>?_) (fun j=>?_) i
  · simp only [RecoveryPrefixLoopDock.tapes,Fin.addCases_left,Function.comp_apply]
    rfl
  · fin_cases j
    exact hi.2.1

theorem loop_ready (flat : Bool) (C payload total : Nat) (ambient : Fin 389→List Bool)
    (hC : 1073741824≤C) (hi : Prepared C payload total ambient) :
    ∃ cost ≤ RecoveryPrefixSearch.budget (RecoveryPrefixColdPrepare.capacity C payload total) total,
      ∃ out : Fin 389→List Bool,
      Ready RecoveryOracle.correctedSat (ports.program (pieces C flat 2)) cost ambient out ∧
      Searched (RecoveryPrefixColdPrepare.capacity C payload total) total (search flat payload total []) out := by
  classical
  obtain ⟨cost,hcost,localOut,lastLog,last,hlocal,_,hout⟩ :=
    RecoveryPrefixSearch.prepared_ready (RecoveryPrefixColdPrepare.capacity C payload total)
      payload total (RecoveryPrefixColdPrepare.capacity C payload total+1) flat false
      (frame (List.replicate total true)) (ambient ∘ nativeSlot) hi.1 (Nat.le_refl _)
      (capacity_covers C payload total hC)
  have h := hlocal.focus ports loopSlots loop_injective (loop_query flat) ambient (loop_input flat C payload total ambient hi)
  refine ⟨cost,hcost,_,h,?_,?_,?_⟩
  · change install loopSlots ambient _ (loopSlots 1)=_
    rw [install_slot _ loop_injective]
    change localOut 1=_
    exact hout.prefixField
  · change install loopSlots ambient _ (loopSlots 360)=_
    rw [install_slot _ loop_injective]
    change RecoveryPrefixLoopDock.tapes (RecoveryPrefixBody.program flat) total localOut
      ((0 : Fin 1).natAdd 360)=_
    simp only [RecoveryPrefixLoopDock.tapes,Fin.addCases_right]
  · intro i hlarge
    rw [install_other _ _ _ _ (by
      intro j he
      have hv:=congrArg (fun k : Fin 389=>k.val) he
      have hj:=j.isLt
      dsimp [loopSlots] at hv
      omega)]
    exact hi.2.2 i hlarge

end NearCubicWires.RepairSource.RecoveryPrefixCold
