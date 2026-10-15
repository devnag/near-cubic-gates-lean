import Proof.MachineModel.OrdinaryWilliamsPositive
import Proof.MachineModel.OrdinaryWilliamsZeroGate

/-! Constant canonical zero dispatch on the same external-input tapes.
Both outcomes retain the literal input and restore every head. -/
namespace NearCubicWires.RepairOrdinary.WilliamsCall
open LocalBitMultitape RepairRepresentation SourceInterfaces ExecutableInterfaces WilliamsLoaderForms
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def gateSlot (a : WilliamsAlgorithm) : Fin 1 → Fin (tapeCount a) := fun _ => ⟨0,by unfold tapeCount; omega⟩
noncomputable def gateMachine (a : WilliamsAlgorithm) : Machine (tapeCount a) 16 :=
  RecoveryFocus.machine (gateSlot a) WilliamsZeroGate.machine

theorem gate_injective (a : WilliamsAlgorithm) : Function.Injective (gateSlot a) :=
  fun _ _ _ => Subsingleton.elim _ _

theorem gate_run (a : WilliamsAlgorithm) (r : RectangularProductRequest) :
    ∃ actual : ExecutionReceipt (tapeCount a) 16,
      run (gateMachine a) 10 (input a r)=some actual ∧ actual.final.tapes=input a r ∧
      (∀ i,actual.final.heads i=0) ∧ actual.final.control=(if r.dimension=0 then 15 else 10) ∧ actual.steps ≤ 10 := by
  obtain ⟨base,hb,ht,hh,hc,_,_,hs⟩ := WilliamsZeroGate.gate_run r.dimension (WilliamsPayloadCount.payload r)
  let entry := initialConfiguration (gateMachine a) (input a r)
  let part := initialConfiguration WilliamsZeroGate.machine (fun _ => WilliamsZeroGate.request r.dimension (WilliamsPayloadCount.payload r))
  have hi : RecoveryFocus.config (gateSlot a) entry.heads entry.tapes part=entry := by
    apply WilliamsSourceCrop.focus_same
    · intro i; rfl
    · intro i; rfl
  obtain ⟨actual,ha,hf,hsteps⟩ := RecoveryFocus.run_config (gateSlot a) (gate_injective a) WilliamsZeroGate.machine
    entry.heads entry.tapes 10 part base hb
  rw [hi] at ha
  refine ⟨actual,ha,?_,?_,?_,hsteps.trans_le hs⟩
  · rw [hf]
    funext i
    cases hp : RecoveryFocus.pick (gateSlot a) i with
    | none => simp only [RecoveryFocus.config,hp]; rfl
    | some j =>
      have hij := RecoveryFocus.slot_of_pick (gateSlot a) hp
      simp only [RecoveryFocus.config,hp]
      rw [ht,←hij]
      rfl
  · intro i
    rw [hf]
    cases hp : RecoveryFocus.pick (gateSlot a) i with
    | none => simp only [RecoveryFocus.config,hp]; rfl
    | some j => simpa only [RecoveryFocus.config,hp] using hh j
  · rw [hf]; exact hc

end NearCubicWires.RepairOrdinary.WilliamsCall
