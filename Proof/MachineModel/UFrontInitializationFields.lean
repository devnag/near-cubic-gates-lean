import Proof.MachineModel.UFrontRun

/-! The actual successful front supplies the two initialization sources and
all three width words at their required physical heads. -/
namespace NearCubicWires.RepairOrdinary.UFront
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def InitializationFields (raw : List Bool) (heads : Fin 81 → ℕ) (tapes : Fin 81 → List Bool) : Prop :=
  ∃ x choices : List Bool,
    2≤ClockDyadicLedger.limit raw.length ∧ x.length≤choices.length ∧
    choices.length≤ClockDyadicLedger.limit raw.length ∧
    tapes 8=frame x ∧ tapes 78=frame choices ∧
    tapes 20=List.replicate (ClockDyadicLedger.width raw.length) true ∧
    tapes 21=List.replicate (2*ClockDyadicLedger.width raw.length) true ∧
    tapes 22=List.replicate (2*ClockDyadicLedger.width raw.length+2) true ∧
    heads 8=0 ∧ heads 78=0 ∧ heads 20=0 ∧ heads 21=0 ∧ heads 22=0

theorem initialization_fields {s : ℕ} (raw witness : List Bool) (final : Configuration 81 s)
    (h : Successful raw witness final) (hbit : final.scanned 79=true) :
    InitializationFields raw final.heads final.tapes := by
  obtain ⟨code,x,bound,padding,base,last,he,hg,_,hb,hh,ht,ho,hpres⟩ := h
  have hlast : last.scanned 79=true := by simpa only [Configuration.scanned,hh,ht] using hbit
  obtain ⟨_,hw,_,hvalid,hgood⟩ := UWitnessOrdinary.literal_abi
    (ClockDyadicLedger.width raw.length) (RadixSemantics.value bound) witness last ho
  obtain ⟨_,_,hchoices,_,_,hheads⟩ := hgood hlast
  have hv := hvalid.mp hlast
  obtain ⟨code',x',bound',padding',he',_,_,_,hx,_,hI,hK,_,_,h8,_,h21,h22,_⟩ :=
    UDecoder.successful_fields raw witness base hb
  obtain ⟨rfl,rfl,rfl,rfl⟩ := UInputEntry.source_unique _ _ _ _ _ _ _ _ (he.symm.trans he')
  have hr (i : Fin 69) (hi : ∀ j,UWitnessOrdinary.slots j≠i.castAdd 12) :
      final.heads (i.castAdd 12)=base.heads i ∧ final.tapes (i.castAdd 12)=base.tapes i := by
    have hk := hpres (i.castAdd 12) hi
    simpa [hh,ht,extended,TapeEmbedding.config] using hk
  have hkeep8 := hr 8 (by intro j; fin_cases j <;> decide)
  have hkeep21 := hr 21 (by intro j; fin_cases j <;> decide)
  have hkeep22 := hr 22 (by intro j; fin_cases j <;> decide)
  have hN : 2≤raw.length := by
    rw [he]
    simp only [VerifierInputFields.source,List.length_append,frame_length]
    omega
  have hL : 2≤ClockDyadicLedger.limit raw.length :=
    hN.trans (ClockEnvelope.input_le_limit raw.length)
  have hc : ((witness.drop (ClockDyadicLedger.width raw.length)).take (RadixSemantics.value bound)).length=
      RadixSemantics.value bound := by
    simp only [List.length_take,List.length_drop]
    apply Nat.min_eq_left
    have := hv.2.2
    omega
  refine ⟨x,(witness.drop (ClockDyadicLedger.width raw.length)).take (RadixSemantics.value bound),
    hL,by rw [hc]; exact hg.2.1,by rw [hc]; exact hg.2.2,
    hkeep8.2.trans hx,by rw [ht]; exact hchoices,by rw [ht]; exact hw,
    hkeep21.2.trans hI,hkeep22.2.trans hK,hkeep8.1.trans h8,?_,?_,
    hkeep21.1.trans h21,hkeep22.1.trans h22⟩
  · rw [hh]
    exact hheads 12 (by decide) (by decide)
  · rw [hh]
    exact hheads 1 (by decide) (by decide)

end NearCubicWires.RepairOrdinary.UFront
