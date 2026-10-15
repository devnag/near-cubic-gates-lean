import Proof.MachineModel.UFrontInitializationFields

/-! The retained front endpoint ties the physical witness cursor and binary
m field to the same input and choice words consumed by initialization. -/
namespace NearCubicWires.RepairOrdinary.UFront
open LocalBitMultitape RecoveryExecution SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem frame_injective : Function.Injective frame := by
  intro a b h
  induction a generalizing b with
  | nil => cases b <;> simp_all [frame]
  | cons bit bits ih =>
    cases b with
    | nil => simp [frame] at h
    | cons bit' bits' =>
      simp only [frame,List.cons.injEq,true_and] at h
      exact congrArg₂ List.cons h.1 (ih h.2)

def WitnessFields (raw witness x choices : List Bool)
    (heads : Fin 81 → ℕ) (tapes : Fin 81 → List Bool) : Prop :=
  ∃ word bound padding m suffix,
    raw=VerifierInputFields.source word x bound padding ∧ UInputScalars.Guards raw x bound ∧
    witness=binary (ClockDyadicLedger.width raw.length) m++choices++suffix ∧
    m≤choices.length ∧ choices.length=RadixSemantics.value bound ∧
    tapes 1=frame witness ∧ heads 1=2*(ClockDyadicLedger.width raw.length+choices.length) ∧
    tapes 74=frame (binary (ClockDyadicLedger.width raw.length) m) ∧ heads 74=0

theorem witness_fields {s : ℕ} (raw witness x choices : List Bool) (final : Configuration 81 s)
    (h : Successful raw witness final) (hbit : final.scanned 79=true)
    (hx : final.tapes 8=frame x) (hc : final.tapes 78=frame choices) :
    WitnessFields raw witness x choices final.heads final.tapes := by
  obtain ⟨word,x0,bound,padding,base,last,he,hg,_,hb,hh,ht,ho,hpres⟩ := h
  have hlast : last.scanned 79=true := by simpa only [Configuration.scanned,hh,ht] using hbit
  obtain ⟨hwit,_,_,hvalid,hgood⟩ := UWitnessOrdinary.literal_abi
    (ClockDyadicLedger.width raw.length) (RadixSemantics.value bound) witness last ho
  obtain ⟨hpos,hm,hchoices,_,_,hheads⟩ := hgood hlast
  obtain ⟨m,choices0,suffix,hwitness,hmB,hB,hme,hce,_⟩ := UWitness.successful_prefix
    (ClockDyadicLedger.width raw.length) (RadixSemantics.value bound) witness (hvalid.mp hlast)
  obtain ⟨word',x',bound',padding',he',_,_,_,hx0,_⟩ := UDecoder.successful_fields raw witness base hb
  obtain ⟨rfl,rfl,rfl,rfl⟩ := UInputEntry.source_unique _ _ _ _ _ _ _ _ (he.symm.trans he')
  have hk := hpres 8 (by intro k; fin_cases k <;> decide)
  have hxbase : final.tapes 8=frame x0 := by
    rw [ht]
    exact hk.2.trans hx0
  have hxx : x=x0 := frame_injective (hx.symm.trans hxbase)
  subst x0
  have hcc : choices=choices0 := by
    apply frame_injective
    rw [hce]
    exact hc.symm.trans ((congrFun ht 78).trans hchoices)
  have hB' : choices.length=RadixSemantics.value bound := by rw [hcc]; exact hB
  refine ⟨word,bound,padding,m,suffix,he,hg,?_,by rwa [hB'],hB',?_,?_,?_,?_⟩
  · simpa only [←hcc] using hwitness
  · exact (congrFun ht 1).trans hwit
  · exact (congrFun hh 1).trans (by simpa only [hB'] using hpos)
  · exact (congrFun ht 74).trans (by simpa only [hme] using hm)
  · exact (congrFun hh 74).trans (hheads 8 (by decide) (by decide))

end NearCubicWires.RepairOrdinary.UFront
