import Proof.MachineModel.UWalkBootstrapPadding

/-! Apply the139-tape bootstrap to the actual initialized ordinary machine
state, discharging the one logical old-counter zero tail by reverse padding. -/
namespace NearCubicWires.RepairOrdinary.UWalkBootstrap
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem entry_run {s : ℕ} (raw witness : List Bool) (base : Configuration 97 s)
    (hp : UInitialized.Prepared raw witness base) :
    ∃ c t j,c ≤ Nat.log 2 raw.length ∧ t ≤ c ∧ j ≤ c ∧
      ZeroPadding.pad (c+2) (base.tapes 50)=CapMachine.counter c t ∧
      base.tapes 58=CompareMachine.word j ∧
    ∃ r,runFrom UWalkArray.machine (UWalkArray.budget (ClockDyadicLedger.width raw.length) t j) (entry base)=some r ∧
      UWalkArray.Numeric (ClockDyadicLedger.width raw.length) t j c (ZeroPadding.config (capacity c) r.final) ∧
      (∀ i : Fin 97,i.val≠20 → i.val≠50 → i.val≠58 → i.val≠73 →
        r.final.tapes (i.castAdd 42)=base.tapes i ∧ r.final.heads (i.castAdd 42)=base.heads i) ∧
      r.final.tapes 136=(List.replicate t (frame (binary (ClockDyadicLedger.width raw.length) 0))).flatten ∧
      (∀ i,135 ≤ i.val → r.final.heads i=0) ∧
      r.steps ≤ 32768*(c+1)*(ClockDyadicLedger.width raw.length+1) := by
  obtain ⟨c,t,j,hc,htc,hjc,hw,htt,hjt,hwt,hh⟩ := UInitialized.walk_fields raw witness base hp
  have hwidth : 1 ≤ ClockDyadicLedger.width raw.length := by simp [ClockDyadicLedger.width]
  let padded := ZeroPadding.config (capacity c) base
  have ht : padded.tapes 20=List.replicate (ClockDyadicLedger.width raw.length) true ∧
      padded.tapes 50=CapMachine.counter c t ∧ padded.tapes 58=CompareMachine.word j ∧
      padded.tapes 73=CompareMachine.word (ClockDyadicLedger.width raw.length) := by
    simpa [padded,ZeroPadding.config,capacity] using And.intro hw (And.intro htt (And.intro hjt hwt))
  obtain ⟨logical,hlogical,hnum,hpres,harray,hheads,hsteps⟩ := UWalkArray.literal_run
    (ClockDyadicLedger.width raw.length) t j c hwidth padded.heads padded.tapes hh ht
  change runFrom UWalkArray.machine (UWalkArray.budget (ClockDyadicLedger.width raw.length) t j)
    (entry padded)=some logical at hlogical
  have he := entry_padding c base
  change ZeroPadding.config (capacity c) (entry base)=entry padded at he
  rw [←he] at hlogical
  obtain ⟨r,hr,hf,hrs,_⟩ := ZeroPadding.run_unpad UWalkArray.machine (capacity c) _ _ logical hlogical
  refine ⟨c,t,j,hc,htc,hjc,htt,hjt,r,hr,?_,?_,?_,?_,hrs.trans_le (hsteps.trans (UWalkArray.budget_short _ _ _ c htc hjc))⟩
  · rw [hf]
    exact hnum
  · intro i hi20 hi50 hi58 hi73
    have h := hpres i hi20 hi50 hi58 hi73
    rw [←hf] at h
    simpa [ZeroPadding.config,capacity,hi50,padded] using h
  · have h := harray
    rw [←hf] at h
    simpa [ZeroPadding.config,capacity] using h
  · intro i hi
    have h := hheads i hi
    rw [←hf] at h
    exact h

end NearCubicWires.RepairOrdinary.UWalkBootstrap
