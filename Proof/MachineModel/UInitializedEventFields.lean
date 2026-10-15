import Proof.MachineModel.UInitializedRun

/-! The executed initialization supplies the walk's continuous serial,
event append cursor and physical serial-width driver. Zero padding records
only the existing serial tape's trailing blank cells. -/
namespace NearCubicWires.RepairOrdinary.UInitialized
open LocalBitMultitape RecoveryExecution SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def EventFields (w : ℕ) (x choices : List Bool)
    (heads : Fin 97 → ℕ) (tapes : Fin 97 → List Bool) : Prop :=
  ZeroPadding.pad (2*w) (tapes 91)=binary (2*w) (2*x.length+2*choices.length+2) ∧
  tapes 21=List.replicate (2*w) true ∧
  tapes 92=MemoryInitialEmission.fields (2*w) (2*w+2) w 0
    (MemoryInitialization.events x choices) ∧
  heads 91=0 ∧ heads 21=0 ∧ heads 92=(tapes 92).length

theorem local_event_fields (w : ℕ) (x choices : List Bool)
    (localFinal : Configuration 21 179) (hl : LocalResult w x choices localFinal) :
    ZeroPadding.pad (2*w) (localFinal.tapes 15)=binary (2*w) (2*x.length+2*choices.length+2) ∧
    localFinal.tapes 12=List.replicate (2*w) true ∧
    localFinal.tapes 16=MemoryInitialEmission.fields (2*w) (2*w+2) w 0
      (MemoryInitialization.events x choices) ∧
    localFinal.heads 15=0 ∧ localFinal.heads 12=0 ∧
    localFinal.heads 16=(localFinal.tapes 16).length := by
  obtain ⟨small,hh,ht,he⟩ := hl
  have hhead (k : Fin 11) : localFinal.heads (UInitialization.memorySlots k)=
      (memoryEndpoint w x choices).heads k := by
    rw [hh]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot _ UInitialization.memory_injective]
    exact congrArg (fun c => c.heads k) he
  have htape (k : Fin 11) :
      ZeroPadding.pad (MemoryInitializationCarrier.capacities w k)
        (localFinal.tapes (UInitialization.memorySlots k))=(memoryEndpoint w x choices).tapes k := by
    rw [ht]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot _ UInitialization.memory_injective]
    exact congrArg (fun c => c.tapes k) he
  have hserial := htape 0
  have hwidth := htape 1
  have hout := htape 2
  have hs := hhead 0
  have hI := hhead 1
  have ho := hhead 2
  simp [UInitialization.memorySlots,MemoryInitializationCarrier.capacities,
    memoryEndpoint,MemoryInitialSources.config,MemoryInitialCell.config,MemoryRecordEmitter.config,
    TapeEmbedding.config,Fin.addCases,
    ZeroPadding.pad_zero,binary_length,frame_length] at hserial hwidth hout hs hI ho
  refine ⟨?_,hwidth,hout,hs,hI,?_⟩
  · exact hserial.trans (congrArg (binary (2*w)) (by omega))
  · rw [hout]
    exact ho

theorem event_fields {s : ℕ} (raw witness : List Bool) (final : Configuration 97 s)
    (hp : Prepared raw witness final) :
    ∃ x choices, x.length≤choices.length ∧ choices.length≤ClockDyadicLedger.limit raw.length ∧
      EventFields (ClockDyadicLedger.width raw.length) x choices final.heads final.tapes := by
  obtain ⟨base,x,choices,localFinal,_,_,hn,hB,_,_,hh,ht,hl,_⟩ := hp
  obtain ⟨hserial,hwidth,hout,hs,hI,ho⟩ := local_event_fields _ x choices localFinal hl
  have hhead (k : Fin 21) : final.heads (UInitializationAmbient.slots k)=localFinal.heads k := by
    rw [hh]
    simp [RecoveryFocus.config,RecoveryFocus.pick_slot _ UInitializationAmbient.slots_injective]
  have htape (k : Fin 21) : final.tapes (UInitializationAmbient.slots k)=localFinal.tapes k := by
    rw [ht]
    simp [RecoveryFocus.config,RecoveryFocus.pick_slot _ UInitializationAmbient.slots_injective]
  refine ⟨x,choices,hn,hB,?_,(htape 12).trans hwidth,(htape 16).trans hout,
    (hhead 15).trans hs,(hhead 12).trans hI,?_⟩
  · exact (congrArg (ZeroPadding.pad (2*ClockDyadicLedger.width raw.length)) (htape 15)).trans hserial
  · exact (hhead 16).trans (ho.trans (congrArg List.length (htape 16)).symm)

end NearCubicWires.RepairOrdinary.UInitialized
