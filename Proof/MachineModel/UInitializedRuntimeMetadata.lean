import Proof.MachineModel.UDecoderRuntimeTransport
import Proof.MachineModel.UInitializedCalls

/-! The physical witness and initialization phases retain the same eight
decoder fields, including every cursor and every existing zero-tail relation.
The original successful decoder snapshot remains explicit. -/
namespace NearCubicWires.RepairOrdinary
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem UFront.runtime_witness_outside (i : Fin 69) (hi : UDecoder.RuntimeSlot i) :
    ∀ j,UWitnessOrdinary.slots j≠i.castAdd 12 := by
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

theorem UFront.runtime_origin {s : ℕ} (raw witness : List Bool) (final : Configuration 81 s)
    (h : UFront.Successful raw witness final) :
    UDecoder.RuntimeOrigin raw witness (fun i => final.heads (i.castAdd 12))
      (fun i => final.tapes (i.castAdd 12)) := by
  obtain ⟨_,_,_,_,base,last,_,_,ha,hbase,hh,ht,_,hpres⟩ := h
  refine ⟨base,ha,hbase,?_⟩
  intro i hi
  have hk := hpres (i.castAdd 12) (UFront.runtime_witness_outside i hi)
  simpa [hh,ht,UFront.extended,TapeEmbedding.config] using hk

theorem UFront.runtime_metadata {s : ℕ} (raw witness : List Bool) (final : Configuration 81 s)
    (h : UFront.Successful raw witness final) :
    ∃ v word,UDecoder.RuntimeMetadata raw.length (fun i => final.heads (i.castAdd 12))
      (fun i => final.tapes (i.castAdd 12)) v word :=
  (UFront.runtime_origin raw witness final h).metadata

theorem UInitialized.runtime_initialization_outside (i : Fin 69) (hi : UDecoder.RuntimeSlot i) :
    ∀ j,UInitializationAmbient.slots j≠i.castAdd 28 := by
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

theorem UInitialized.runtime_focus_preserved {s : ℕ} (base : Configuration 81 s)
    (localFinal : Configuration 21 179) (i : Fin 69) (hi : UDecoder.RuntimeSlot i) :
    (RecoveryFocus.config UInitializationAmbient.slots
      (UInitializationAmbient.extended base).heads (UInitializationAmbient.extended base).tapes localFinal).heads
        (i.castAdd 28)=base.heads (i.castAdd 12) ∧
    (RecoveryFocus.config UInitializationAmbient.slots
      (UInitializationAmbient.extended base).heads (UInitializationAmbient.extended base).tapes localFinal).tapes
        (i.castAdd 28)=base.tapes (i.castAdd 12) := by
  have he : (i.castAdd 12).castAdd 16=i.castAdd 28 := by apply Fin.ext; rfl
  have hnone := UWitness.pick_other UInitializationAmbient.slots (i.castAdd 28)
    (UInitialized.runtime_initialization_outside i hi)
  rw [←he] at hnone ⊢
  simp [RecoveryFocus.config,hnone,UInitializationAmbient.extended,TapeEmbedding.config]

theorem UInitialized.runtime_origin {s : ℕ} (raw witness : List Bool) (final : Configuration 97 s)
    (hp : UInitialized.Prepared raw witness final) :
    UDecoder.RuntimeOrigin raw witness (fun i => final.heads (i.castAdd 28))
      (fun i => final.tapes (i.castAdd 28)) := by
  obtain ⟨base,_,_,localFinal,hbase,_,_,_,_,_,hh,ht,_,_⟩ := hp
  obtain ⟨decoder,ha,hd,hkeep⟩ := UFront.runtime_origin raw witness base hbase
  refine ⟨decoder,ha,hd,?_⟩
  intro i hi
  have hr := UInitialized.runtime_focus_preserved base localFinal i hi
  have hk := hkeep i hi
  exact ⟨(congrFun hh (i.castAdd 28)).trans (hr.1.trans hk.1),
    (congrFun ht (i.castAdd 28)).trans (hr.2.trans hk.2)⟩

theorem UInitialized.runtime_metadata {s : ℕ} (raw witness : List Bool) (final : Configuration 97 s)
    (hp : UInitialized.Prepared raw witness final) :
    ∃ v word,UDecoder.RuntimeMetadata raw.length (fun i => final.heads (i.castAdd 28))
      (fun i => final.tapes (i.castAdd 28)) v word :=
  (UInitialized.runtime_origin raw witness final hp).metadata

end NearCubicWires.RepairOrdinary
