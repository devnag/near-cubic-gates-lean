import Proof.MachineModel.UDecoderRuntimeDrivers
import Proof.MachineModel.UFrontRun

/-! The successful witness phase retains the decoder drivers and supplies
the width sentinel used by the physical walk bootstrap. -/
namespace NearCubicWires.RepairOrdinary.UFront
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def WalkDrivers (raw : List Bool) (heads : Fin 81 → ℕ) (tapes : Fin 81 → List Bool) : Prop :=
  ∃ c t j,c ≤ Nat.log 2 raw.length ∧ t ≤ c ∧ j ≤ c ∧
    ZeroPadding.pad (c+2) (tapes 50)=CapMachine.counter c t ∧
    tapes 58=CompareMachine.word j ∧ tapes 73=CompareMachine.word (ClockDyadicLedger.width raw.length) ∧
    heads 50=1 ∧ heads 58=1 ∧ heads 73=1

theorem walk_drivers {s : ℕ} (raw witness : List Bool) (final : Configuration 81 s)
    (h : Successful raw witness final) (hbit : final.scanned 79=true) :
    WalkDrivers raw final.heads final.tapes := by
  obtain ⟨code,x,bound,padding,base,last,_,_,ha,hbase,hh,ht,ho,hpres⟩ := h
  obtain ⟨c,t,j,hc,htc,hjc,htt,hjt,hth,hjh⟩ := UDecoder.successful_runtime_drivers raw witness base hbase ha
  have hlast : last.scanned 79=true := by simpa only [Configuration.scanned,hh,ht] using hbit
  obtain ⟨_,_,_,_,hgood⟩ := UWitnessOrdinary.literal_abi
    (ClockDyadicLedger.width raw.length) (RadixSemantics.value bound) witness last ho
  obtain ⟨_,_,_,hwt,hwh,_⟩ := hgood hlast
  have hkeep50 := hpres 50 (by intro k; fin_cases k <;> decide)
  have hkeep58 := hpres 58 (by intro k; fin_cases k <;> decide)
  have he50 : final.heads 50=base.heads 50 ∧ final.tapes 50=base.tapes 50 := by
    simpa [hh,ht,extended,TapeEmbedding.config,Fin.addCases] using hkeep50
  have he58 : final.heads 58=base.heads 58 ∧ final.tapes 58=base.tapes 58 := by
    simpa [hh,ht,extended,TapeEmbedding.config,Fin.addCases] using hkeep58
  refine ⟨c,t,j,hc,htc,hjc,?_,he58.2.trans hjt,?_,he50.1.trans hth,he58.1.trans hjh,?_⟩
  · rw [he50.2]
    exact htt
  · rw [ht]
    exact hwt
  · rw [hh]
    exact hwh

end NearCubicWires.RepairOrdinary.UFront
