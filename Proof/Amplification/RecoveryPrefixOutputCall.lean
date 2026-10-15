import Proof.Amplification.RecoveryPrefixLoopCall

/-! Actual final calls of the cold prefix search: seal the retained unary
driver and use its executed doubled length to copy exactly the selected bits. -/
namespace NearCubicWires.RepairSource.RecoveryPrefixCold
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Sealed (cap total : Nat) (xs : List Bool) (ambient : Fin 389→List Bool) : Prop :=
  ambient 2=ZeroPadding.pad cap (frame (xs++[false,true])) ∧
  ambient 361=UnaryTemplate.tape total ∧
  ∀ i : Fin 389,382 ≤ i.val → i.val<388 → ambient i=[]

theorem seal_ready (cap total : Nat) (xs : List Bool) (ambient : Fin 389→List Bool)
    (hi : Searched cap total xs ambient) : ∃ out,
    ClockJoin.ReadyRun sealProgram (2*total+6) ambient out ∧ Sealed cap total xs out := by
  classical
  have h := (RecoveryPrefixDriverSeal.seal_ready total).focus sealSlots seal_injective ambient (by
    intro i
    fin_cases i
    · exact hi.2.1
    · exact hi.2.2 388 (by decide))
  refine ⟨_,h,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by intro i; fin_cases i <;> decide)]
    exact hi.1
  · change install sealSlots ambient _ (sealSlots 0)=_
    rw [install_slot _ seal_injective]
    rfl
  · intro i hlo hhi
    rw [install_other _ _ _ _ (by
      intro j he
      have hv:=congrArg (fun k : Fin 389=>k.val) he
      fin_cases j <;> dsimp [sealSlots] at hv <;> omega)]
    exact hi.2.2 i hlo

theorem output_ready (cap total : Nat) (xs : List Bool) (ambient : Fin 389→List Bool)
    (hlen : xs.length=total) (hi : Sealed cap total xs ambient) : ∃ out,
    ClockJoin.ReadyRun output (RecoveryPrefixOutput.budget total) ambient out ∧ out 386=frame xs := by
  classical
  obtain ⟨localOut,hlocal,_,_,hvalue⟩ := RecoveryPrefixOutput.output_ready xs cap
  rw [hlen] at hlocal
  have h := hlocal.focus outputSlots output_injective ambient (by
    intro i
    fin_cases i
    · exact hi.1
    · exact hi.2.1
    · exact hi.2.2 382 (by decide) (by decide)
    · exact hi.2.2 383 (by decide) (by decide)
    · exact hi.2.2 384 (by decide) (by decide)
    · exact hi.2.2 385 (by decide) (by decide)
    · exact hi.2.2 386 (by decide) (by decide)
    · exact hi.2.2 387 (by decide) (by decide))
  refine ⟨_,h,?_⟩
  change install outputSlots ambient localOut (outputSlots 6)=_
  rw [install_slot _ output_injective]
  exact hvalue

end NearCubicWires.RepairSource.RecoveryPrefixCold
