import Proof.Amplification.RecoveryViewBankWhole

/-! All scalar sources for the raw-view bank come from the actual cold
header and the successful valuation return. New bank tapes start blank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def lift (a : Fin 32→List Bool) (i : Fin 100) : List Bool :=
  Fin.addCases a (fun _ : Fin 68=>[]) i

theorem cap_kept (bits : List Bool) (c s : Nat) (j : Fin 20) (hj : j.val≠1) :
    RecoveryColdHeaderCap.output bits c s (j.castAdd 2)=RecoveryColdHeader.output bits c s j := by
  have ho : ∀ k,RecoveryColdHeaderCap.slots k≠j.castAdd 2 := by
    intro k he
    have hv : (RecoveryColdHeaderCap.slots k).val=j.val := congrArg (fun x : Fin 22=>x.val) he
    have hb := j.isLt
    fin_cases k
    · change 1=j.val at hv
      exact hj hv.symm
    · change 20=j.val at hv
      omega
    · change 21=j.val at hv
      omega
  unfold RecoveryColdHeaderCap.output
  rw [install_other RecoveryColdHeaderCap.slots _ _ _ ho]
  simp only [RecoveryColdHeaderCap.ambient,Fin.addCases_left]

theorem preliminary_sources (bits word : List Bool) (c s : Nat) :
    RecoveryColdPreliminary.output bits word c s 2=CompareMachine.word (width bits) ∧
    RecoveryColdPreliminary.output bits word c s 6=frame (RecoveryColdHeader.codeWord bits) ∧
    RecoveryColdPreliminary.output bits word c s 8=frame (RecoveryColdHeader.boundWord bits) ∧
    RecoveryColdPreliminary.output bits word c s 16=List.replicate (erase bits) true := by
  have hw := (RecoveryColdPreliminary.header_retained bits word c s 1).trans
    (install_slot RecoveryColdHeaderCap.slots RecoveryColdHeaderCap.slots_injective _ _ 0)
  change RecoveryColdPreliminary.output bits word c s 2=
    RecoveryColdCap.word (max 1 bits.length+1+1) at hw
  have hc : RecoveryColdHeader.output bits c s 5=frame (RecoveryColdHeader.codeWord bits) :=
    install_slot RecoveryColdHeader.driverSlots RecoveryColdHeader.driverSlots_injective _ _ 0
  have hb : RecoveryColdHeader.output bits c s 7=frame (RecoveryColdHeader.boundWord bits) :=
    install_other RecoveryColdHeader.driverSlots _ _ _ (by intro k; fin_cases k <;> decide)
  have he := install_slot RecoveryColdHeader.driverSlots RecoveryColdHeader.driverSlots_injective
    (RecoveryColdHeader.base bits c s (RecoveryColdHeader.fields3 bits))
    (RecoveryEraseDriver.output3 (RecoveryColdHeader.codeWord bits)) (4 : Fin 9)
  have her : RecoveryColdHeader.output bits c s 15=List.replicate (erase bits) true := by
    change RecoveryColdHeader.output bits c s 15=
      List.replicate (8192*((RecoveryColdHeader.codeWord bits).length+1)*((RecoveryColdHeader.codeWord bits).length+1)) true at he
    rw [RecoveryColdHeader.code_length] at he
    simpa only [erase,RecoveryColdValuation.capacity,RecoveryColdValuation.width,pow_two,Nat.mul_assoc] using he
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [width,RecoveryColdValuation.width,RecoveryColdHeader.width,RecoveryColdWidth.width,
      RecoveryColdCap.word,Nat.add_assoc] using hw
  · exact (RecoveryColdPreliminary.header_retained bits word c s 5).trans
      ((cap_kept bits c s 5 (by decide)).trans hc)
  · exact (RecoveryColdPreliminary.header_retained bits word c s 7).trans
      ((cap_kept bits c s 7 (by decide)).trans hb)
  · exact (RecoveryColdPreliminary.header_retained bits word c s 15).trans
      ((cap_kept bits c s 15 (by decide)).trans her)

theorem sources_of_return (bits word : List Bool) (c s : Nat) (a : Fin 32→List Bool)
    (hz : a 10=frame (RecoveryColdHeader.zeroWord bits))
    (hc : a 21=CompareMachine.word (limit bits))
    (hout : ∀ i,(∀ j,RecoveryColdValuation.slots j≠i) → a i=RecoveryColdValuation.after bits word c s i) :
    Sources bits (lift a) := by
  obtain ⟨hw,hcode,hbound,he⟩ := preliminary_sources bits word c s
  constructor
  · change a 2=_
    rw [hout 2 (by intro j; fin_cases j <;> decide)]
    exact hw
  · change a 6=_
    rw [hout 6 (by intro j; fin_cases j <;> decide)]
    exact hcode
  · change a 8=_
    rw [hout 8 (by intro j; fin_cases j <;> decide)]
    exact hbound
  · exact hz
  · change a 16=_
    rw [hout 16 (by intro j; fin_cases j <;> decide)]
    exact he
  · exact hc
  · intro i hi
    simp [lift,Fin.addCases,show ¬i.val<32 by omega]

end NearCubicWires.RepairOrdinary.RecoveryColdView
