import Proof.MachineModel.UFrontInitializationFields
import Proof.MachineModel.UInitializationRun

/-! Actual initialization runs directly on the successful ordinary front's
five physical inputs. The remaining sixteen workspace tapes are appended blank. -/
namespace NearCubicWires.RepairOrdinary.UInitializationAmbient
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 21 → Fin 97 := ![20,81,82,83,84,85,22,86,87,88,89,90,21,8,78,91,92,93,94,95,96]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def machine : Machine 97 179 := RecoveryFocus.machine slots UInitialization.machine
def extended {s : ℕ} (base : Configuration 81 s) : Configuration 97 s :=
  TapeEmbedding.config (fun _ : Fin 16 => 0) (fun _ : Fin 16 => []) base
noncomputable def entry {s : ℕ} (base : Configuration 81 s) : Configuration 97 179 :=
  RecoveryCalls.restarted machine (extended base).heads (extended base).tapes

theorem projected_entry {s : ℕ} (w : ℕ) (x choices : List Bool) (base : Configuration 81 s)
    (hx : base.tapes 8=frame x) (hc : base.tapes 78=frame choices)
    (hw : base.tapes 20=List.replicate w true)
    (hI : base.tapes 21=List.replicate (2*w) true)
    (hK : base.tapes 22=List.replicate (2*w+2) true)
    (hh : base.heads 8=0 ∧ base.heads 78=0 ∧ base.heads 20=0 ∧ base.heads 21=0 ∧ base.heads 22=0)
    (j : Fin 21) :
    (extended base).heads (slots j)=0 ∧
      (extended base).tapes (slots j)=UInitialization.tapes w x choices j := by
  fin_cases j <;> simp [extended,slots,TapeEmbedding.config,Fin.addCases,
    UInitialization.tapes,UInitialization.extra,ClockInitialKey.input,ClockInitialKey.K,
    hx,hc,hw,hI,hK,hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2]

theorem entry_run {s : ℕ} (raw : List Bool) (base : Configuration 81 s)
    (hp : UFront.InitializationFields raw base.heads base.tapes) :
    ∃ x choices : List Bool, x.length≤choices.length ∧ choices.length≤ClockDyadicLedger.limit raw.length ∧
      base.tapes 8=frame x ∧ base.tapes 78=frame choices ∧
    ∃ r,∃ localFinal : Configuration 21 179,∃ small : Configuration 11 154,
      runFrom machine (UInitialization.budget (ClockDyadicLedger.width raw.length) x.length choices.length)
        (entry base)=some r ∧
      r.steps≤UInitialization.budget (ClockDyadicLedger.width raw.length) x.length choices.length ∧
      r.final=RecoveryFocus.config slots (extended base).heads (extended base).tapes localFinal ∧
      localFinal.heads=(RecoveryFocus.config UInitialization.memorySlots (fun _ : Fin 21 => 0)
        (UInitialization.afterKey (ClockDyadicLedger.width raw.length) x choices) small).heads ∧
      localFinal.tapes=(RecoveryFocus.config UInitialization.memorySlots (fun _ : Fin 21 => 0)
        (UInitialization.afterKey (ClockDyadicLedger.width raw.length) x choices) small).tapes ∧
      r.final.tapes 92=MemoryInitialEmission.fields (2*ClockDyadicLedger.width raw.length)
        (2*ClockDyadicLedger.width raw.length+2) (ClockDyadicLedger.width raw.length) 0
        (MemoryInitialization.events x choices) ∧
      ZeroPadding.config (MemoryInitializationCarrier.capacities (ClockDyadicLedger.width raw.length)) small=
        MemoryInitialSources.config 153 (2*ClockDyadicLedger.width raw.length)
          (2*ClockDyadicLedger.width raw.length+2) ((frame x).length+(frame choices).length)
          (frame x).length (2^ClockDyadicLedger.width raw.length+(frame choices).length)
          (4*ClockDyadicLedger.width raw.length+5)
          (MemoryInitialEmission.fields (2*ClockDyadicLedger.width raw.length)
            (2*ClockDyadicLedger.width raw.length+2) (ClockDyadicLedger.width raw.length) 0
            (MemoryInitialization.events x choices))
          (frame x) (frame choices) (frame x).length (frame choices).length false := by
  obtain ⟨x,choices,hL,hn,hB,hx,hc,hw,hI,hK,hheads⟩ := hp
  obtain ⟨localRun,small,hloc,hls,hlh,hlt,hevents,hsmall⟩ := UInitialization.producer_run
    (ClockDyadicLedger.limit raw.length) (ClockDyadicLedger.width raw.length) x choices
    hL hn hB (ClockDyadicLedger.width_bounds raw.length).1
  obtain ⟨r,hr,hf,hrs⟩ := RecoveryFocus.run_config slots slots_injective UInitialization.machine
    (extended base).heads (extended base).tapes _ _ localRun hloc
  have hproj := projected_entry (ClockDyadicLedger.width raw.length) x choices base hx hc hw hI hK hheads
  have he := UWitness.focus_config_eq slots slots_injective
    (initialConfiguration UInitialization.machine (UInitialization.tapes (ClockDyadicLedger.width raw.length) x choices))
    (extended base).heads (extended base).tapes (fun j => (hproj j).1) (fun j => (hproj j).2)
  rw [he] at hr
  refine ⟨x,choices,hn,hB,hx,hc,r,localRun.final,small,hr,hrs.trans_le hls,hf,hlh,hlt,?_,hsmall⟩
  change r.final.tapes (slots 16)=_
  simp [hf,RecoveryFocus.config,RecoveryFocus.pick_slot _ slots_injective,hevents]

end NearCubicWires.RepairOrdinary.UInitializationAmbient
