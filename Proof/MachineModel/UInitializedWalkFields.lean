import Proof.MachineModel.UFrontWalkDrivers
import Proof.MachineModel.UInitializedRun

/-! Actual initialized U state supplies every old input of the walk
bootstrap. Only the decoder counter's pre-existing zero-padding relation
is needed; all nonzero numeric and array fields are subsequently produced. -/
namespace NearCubicWires.RepairOrdinary.UInitialized
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def WalkFields (raw : List Bool) (heads : Fin 97 → ℕ) (tapes : Fin 97 → List Bool) : Prop :=
  ∃ c t j,c ≤ Nat.log 2 raw.length ∧ t ≤ c ∧ j ≤ c ∧
    tapes 20=List.replicate (ClockDyadicLedger.width raw.length) true ∧
    ZeroPadding.pad (c+2) (tapes 50)=CapMachine.counter c t ∧
    tapes 58=CompareMachine.word j ∧ tapes 73=CompareMachine.word (ClockDyadicLedger.width raw.length) ∧
    heads 20=0 ∧ heads 50=1 ∧ heads 58=1 ∧ heads 73=1

theorem local_width (w : ℕ) (x choices : List Bool) (localFinal : Configuration 21 179)
    (hl : LocalResult w x choices localFinal) :
    localFinal.heads 0=0 ∧ localFinal.tapes 0=List.replicate w true := by
  obtain ⟨small,hh,ht,_⟩ := hl
  have hnone := UWitness.pick_other UInitialization.memorySlots (0 : Fin 21)
    (by intro k; fin_cases k <;> decide)
  simp [hh,ht,RecoveryFocus.config,hnone,UInitialization.afterKey,ClockInitialKey.output,Fin.addCases]

theorem walk_fields {s : ℕ} (raw witness : List Bool) (final : Configuration 97 s)
    (hp : Prepared raw witness final) : WalkFields raw final.heads final.tapes := by
  obtain ⟨base,x,choices,localFinal,hbase,hbit,_,_,_,_,hh,ht,hl,_⟩ := hp
  obtain ⟨c,t,j,hc,htc,hjc,htt,hjt,hwt,hth,hjh,hwh⟩ := UFront.walk_drivers raw witness base hbase hbit
  have hw := local_width (ClockDyadicLedger.width raw.length) x choices localFinal hl
  have hwidth : final.heads 20=0 ∧ final.tapes 20=List.replicate (ClockDyadicLedger.width raw.length) true := by
    have hslot : UInitializationAmbient.slots 0=(20 : Fin 97) := rfl
    rw [←hslot,hh,ht]
    simp [RecoveryFocus.config,RecoveryFocus.pick_slot _ UInitializationAmbient.slots_injective,hw.1,hw.2]
  have hr (i : Fin 81) (hi : ∀ k,UInitializationAmbient.slots k≠i.castAdd 16) :
      final.heads (i.castAdd 16)=base.heads i ∧ final.tapes (i.castAdd 16)=base.tapes i := by
    have hnone := UWitness.pick_other UInitializationAmbient.slots (i.castAdd 16) hi
    simp [hh,ht,RecoveryFocus.config,hnone,UInitializationAmbient.extended,TapeEmbedding.config]
  have h50 := hr 50 (by intro k; fin_cases k <;> decide)
  have h58 := hr 58 (by intro k; fin_cases k <;> decide)
  have h73 := hr 73 (by intro k; fin_cases k <;> decide)
  refine ⟨c,t,j,hc,htc,hjc,hwidth.2,?_,h58.2.trans hjt,h73.2.trans hwt,
    hwidth.1,h50.1.trans hth,h58.1.trans hjh,h73.1.trans hwh⟩
  exact (congrArg (ZeroPadding.pad (c+2)) h50.2).trans htt

end NearCubicWires.RepairOrdinary.UInitialized
