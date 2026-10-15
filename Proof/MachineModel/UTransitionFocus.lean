import Proof.MachineModel.UPreparedSources
import Proof.MachineModel.OrdinaryTransitionWalkRun
import Proof.MachineModel.OrdinaryTransitionWalkInitialConsumer

/-! Fixed157-tape transition ABI. Matching independently padded finite
representations uses the same physical walk with exactly the same steps. -/
namespace NearCubicWires.RepairOrdinary.UTransition
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 42 → Fin 157 :=
  ![6,50,51,52,55,58,59,1,139,140,141,142,143,144,145,146,147,148,149,
    112,68,150,151,152,153,119,132,154,155,113,114,91,21,92,123,136,
    115,116,111,74,127,156]
theorem slots_injective : Function.Injective slots := by decide
abbrev states := Fintype.card (RecoveryCalls.Control TransitionWalk.sizes)
noncomputable def machine : Machine 157 states := RecoveryFocus.machine slots TransitionWalk.machine
def extended {s : ℕ} (base : Configuration 139 s) : Configuration 157 s :=
  TapeEmbedding.config (fun _ : Fin 18 => 0) (fun _ : Fin 18 => []) base
noncomputable def entry (heads : Fin 157 → ℕ) (tapes : Fin 157 → List Bool) :=
  RecoveryCalls.restarted machine heads tapes

theorem run_of_matched (d : TransitionWalk.Store) (fuel : ℕ)
    (source : ExecutionReceipt 42 states)
    (hrun : runFrom TransitionWalk.machine fuel (TransitionWalk.cfg TransitionWalk.machine.start d)=some source)
    (heads : Fin 157 → ℕ) (tapes : Fin 157 → List Bool)
    (physicalCap : Fin 157 → ℕ) (logicalCap : Fin 42 → ℕ)
    (hh : ∀ k,heads (slots k)=(TransitionWalk.cfg TransitionWalk.machine.start d).heads k)
    (ht : ∀ k,ZeroPadding.pad (physicalCap (slots k)) (tapes (slots k))=
      ZeroPadding.pad (logicalCap k) ((TransitionWalk.cfg TransitionWalk.machine.start d).tapes k)) :
    ∃ r,runFrom machine fuel (entry heads tapes)=some r ∧ r.steps=source.steps ∧
      (∀ k,r.final.heads (slots k)=source.final.heads k ∧
        ZeroPadding.pad (physicalCap (slots k)) (r.final.tapes (slots k))=
          ZeroPadding.pad (logicalCap k) (source.final.tapes k)) ∧
      (∀ i,(∀ k,slots k≠i) → r.final.heads i=heads i ∧
        ZeroPadding.pad (physicalCap i) (r.final.tapes i)=ZeroPadding.pad (physicalCap i) (tapes i)) := by
  obtain ⟨padded,hpad,hpf,hps,_⟩ := ZeroPadding.run_config TransitionWalk.machine logicalCap _ _ source hrun
  obtain ⟨ambient,ha,haf,has⟩ := RecoveryFocus.run_config slots slots_injective TransitionWalk.machine
    heads (fun i => ZeroPadding.pad (physicalCap i) (tapes i)) fuel _ padded hpad
  have he := UWitness.focus_config_eq slots slots_injective
    (ZeroPadding.config logicalCap (TransitionWalk.cfg TransitionWalk.machine.start d))
    heads (fun i => ZeroPadding.pad (physicalCap i) (tapes i)) hh ht
  change RecoveryFocus.config slots heads (fun i => ZeroPadding.pad (physicalCap i) (tapes i))
    (ZeroPadding.config logicalCap (TransitionWalk.cfg TransitionWalk.machine.start d))=
      ZeroPadding.config physicalCap (entry heads tapes) at he
  rw [he] at ha
  obtain ⟨r,hr,hf,hs,_⟩ := ZeroPadding.run_unpad machine physicalCap fuel (entry heads tapes) ambient ha
  have hfinal := hf.trans haf
  rw [hpf] at hfinal
  refine ⟨r,hr,hs.trans (has.trans hps),?_,?_⟩
  · intro k
    have hheads := congrArg (fun c => c.heads (slots k)) hfinal
    have htapes := congrArg (fun c => c.tapes (slots k)) hfinal
    simpa only [ZeroPadding.config,RecoveryFocus.config,RecoveryFocus.pick_slot _ slots_injective] using
      And.intro hheads htapes
  · intro i hi
    have hnone := UWitness.pick_other slots i hi
    have hheads := congrArg (fun c => c.heads i) hfinal
    have htapes := congrArg (fun c => c.tapes i) hfinal
    simpa only [ZeroPadding.config,RecoveryFocus.config,hnone] using And.intro hheads htapes

end NearCubicWires.RepairOrdinary.UTransition
