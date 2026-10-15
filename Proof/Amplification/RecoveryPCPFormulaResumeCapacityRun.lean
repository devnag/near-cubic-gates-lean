import Proof.Amplification.RecoveryPCPFormulaResumeCapacity

namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeCapacity
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SourceInterfaces ProjectionNormalization
open RadixSemantics VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem power_away (i : Fin 55) (hi : i.val<35) : ∀ j,powerSlots j≠i := by
  intro j h
  have hv:=congrArg (fun i : Fin 55=>i.val) h
  dsimp [powerSlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

theorem capacity_run (rBits qBits : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget rBits qBits) (input rBits qBits) out ∧
      out 3=CompareMachine.word (value rBits) ∧ out 5=List.replicate (value rBits) true ∧
      out 17=List.replicate (RecoveryProjectionRows.capacity (value rBits)) true ∧
      out 31=CompareMachine.word (value qBits) ∧ out 33=List.replicate (value qBits) true ∧
      out 35=List.replicate (value rBits+value qBits) true ∧
      out 37=List.replicate (RecoverySourceClauseLoad.uniformBudget (value qBits) (value rBits)) true := by
  obtain ⟨dim,hd,d3,d5,d17,d31,d33,db⟩ := dimensions_run rBits qBits
  let sumData : Fin 4→List Bool := ![List.replicate (value rBits) true,List.replicate (value qBits) true,
    List.replicate (value rBits+value qBits) true,List.replicate (value rBits+value qBits+2) false]
  let mid:=install sumSlots dim sumData
  have hs:=(ClockUnarySum.sum_ready (value rBits) (value qBits)).focus sumSlots sum_injective dim (by
    intro i; fin_cases i
    · exact d5
    · exact d33
    · exact db 0
    · exact db 1)
  have first:=ClockJoin.join dimensions sumMachine _ _ _ _ _ hd hs
  obtain ⟨power,hp,p0,p7⟩ := PCPSerializerCapacity.Power.capacity_run 2 536870912 (value rBits+value qBits)
  letI : NeZero (DimensionPolynomial.tapes 2) := ⟨by decide⟩
  have hpower:=hp.focus powerSlots power_injective mid (by
    intro i
    by_cases hi : i.val=0
    · have he : i=⟨0,by decide⟩ := Fin.ext hi
      subst i
      change install sumSlots dim sumData (sumSlots 2)=_
      rw [install_slot sumSlots sum_injective]
      rfl
    · have hn : i≠0 := by intro h; apply hi; exact congrArg (fun i : Fin (DimensionPolynomial.tapes 2)=>i.val) h
      have hlo : 37≤(powerSlots i).val := by dsimp [powerSlots]; split_ifs <;> dsimp <;> omega
      dsimp only [mid]
      rw [install_other _ _ _ _ (by
        intro j h; have hv:=congrArg (fun i : Fin 55=>i.val) h
        fin_cases j <;> dsimp [sumSlots] at hv <;> omega)]
      let k : Fin 20 := ⟨(powerSlots i).val-35,by have hj:=(powerSlots i).isLt; omega⟩
      have he : powerSlots i=k.natAdd 35 := by apply Fin.ext; dsimp [k]; omega
      rw [he,db]
      simp only [DimensionPolynomial.input]
      rw [if_neg hi])
  let out:=install powerSlots mid power
  have whole:=ClockJoin.join summed powerMachine _ _ _ _ _ first hpower
  have retained (i : Fin 55) (hi : i.val<35) : out i=mid i :=
    install_other powerSlots mid power i (power_away i hi)
  refine ⟨out,whole,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [retained 3 (by decide)]
    exact (install_other sumSlots dim sumData 3 (by decide)).trans d3
  · rw [retained 5 (by decide)]
    exact install_slot sumSlots sum_injective dim sumData 0
  · rw [retained 17 (by decide)]
    exact (install_other sumSlots dim sumData 17 (by decide)).trans d17
  · rw [retained 31 (by decide)]
    exact (install_other sumSlots dim sumData 31 (by decide)).trans d31
  · rw [retained 33 (by decide)]
    exact install_slot sumSlots sum_injective dim sumData 1
  · exact (install_slot powerSlots power_injective mid power 0).trans p0
  · have h:=(install_slot powerSlots power_injective mid power 7).trans p7
    change out 37=List.replicate (536870912*(value rBits+value qBits+1)^2) true at h
    simpa only [RecoverySourceClauseLoad.uniformBudget,Nat.add_comm (value rBits) (value qBits)] using h

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeCapacity
