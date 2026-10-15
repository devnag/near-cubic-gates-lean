import Proof.MachineModel.UFrontWitnessFields
import Proof.MachineModel.UInitializedEventFields

/-! One retained initialization snapshot supplies both the witness prefix
and the events for precisely the same x and choices. -/
namespace NearCubicWires.RepairOrdinary.UInitialized
open LocalBitMultitape RecoveryExecution SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def SourceFields (raw witness : List Bool) (heads : Fin 97 → ℕ) (tapes : Fin 97 → List Bool) : Prop :=
  ∃ x choices, x.length≤choices.length ∧ choices.length≤ClockDyadicLedger.limit raw.length ∧
    UFront.WitnessFields raw witness x choices (fun i => heads (i.castAdd 16))
      (fun i => tapes (i.castAdd 16)) ∧
    EventFields (ClockDyadicLedger.width raw.length) x choices heads tapes

theorem source_fields {s : ℕ} (raw witness : List Bool) (final : Configuration 97 s)
    (hp : Prepared raw witness final) : SourceFields raw witness final.heads final.tapes := by
  obtain ⟨base,x,choices,localFinal,hbase,hbit,hn,hB,hx,hc,hh,ht,hl,_⟩ := hp
  obtain ⟨word,bound,padding,m,suffix,he,hg,hw,hm,hB',h1t,h1h,h74t,h74h⟩ :=
    UFront.witness_fields raw witness x choices base hbase hbit hx hc
  have hkeep (i : Fin 81) (hi : ∀ k,UInitializationAmbient.slots k≠i.castAdd 16) :
      final.heads (i.castAdd 16)=base.heads i ∧ final.tapes (i.castAdd 16)=base.tapes i := by
    have hnone := UWitness.pick_other UInitializationAmbient.slots (i.castAdd 16) hi
    simp [hh,ht,RecoveryFocus.config,hnone,UInitializationAmbient.extended,TapeEmbedding.config]
  have h1 := hkeep 1 (by intro k; fin_cases k <;> decide)
  have h74 := hkeep 74 (by intro k; fin_cases k <;> decide)
  have hhead (k : Fin 21) : final.heads (UInitializationAmbient.slots k)=localFinal.heads k := by
    rw [hh]
    simp [RecoveryFocus.config,RecoveryFocus.pick_slot _ UInitializationAmbient.slots_injective]
  have htape (k : Fin 21) : final.tapes (UInitializationAmbient.slots k)=localFinal.tapes k := by
    rw [ht]
    simp [RecoveryFocus.config,RecoveryFocus.pick_slot _ UInitializationAmbient.slots_injective]
  obtain ⟨hserial,hwidth,hout,hs,hI,ho⟩ := local_event_fields _ x choices localFinal hl
  refine ⟨x,choices,hn,hB,⟨word,bound,padding,m,suffix,he,hg,hw,hm,hB',
    h1.2.trans h1t,h1.1.trans h1h,h74.2.trans h74t,h74.1.trans h74h⟩,?_,
    (htape 12).trans hwidth,(htape 16).trans hout,(hhead 15).trans hs,(hhead 12).trans hI,?_⟩
  · exact (congrArg (ZeroPadding.pad (2*ClockDyadicLedger.width raw.length)) (htape 15)).trans hserial
  · exact (hhead 16).trans (ho.trans (congrArg List.length (htape 16)).symm)

end NearCubicWires.RepairOrdinary.UInitialized
