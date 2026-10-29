import SourceAdapters.Machine.CappedOutputSerialize
import Proof.Amplification.RecoveryFocusedMachine
import Proof.Hierarchy.HierarchyFixedWord

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: actual fixed failure word on a fresh output tape. -/
namespace NearCubicGates.Adapters.Machine.Capped.ResultWriter
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
set_option autoImplicit false

def failureBits : List Bool := frame (false::frame [])
def failureSlot (_ : Fin 1) : Fin 6 := 1

theorem failureSlot_injective : Function.Injective failureSlot := fun _ _ _ => Subsingleton.elim _ _

noncomputable def failureMachine : Machine 6 (failureBits.length+1) :=
  RecoveryFocus.machine failureSlot (HierarchyFixedWord.raw failureBits)

theorem failure_run (data : Fin 6 → List Bool) (hblank : data 1=[]) :
    ∃ result, run failureMachine 5 data=some result ∧ result.final.tapes 1=failureBits := by
  obtain ⟨base,hb,hf,_⟩ :=
    (HierarchyFixedWord.write_prefix failureBits 0 failureBits.length (by omega)).run
      (by simp [HierarchyFixedWord.raw,HierarchyFixedWord.cfg])
  obtain ⟨result,hr,hrt,_⟩ := RecoveryFocus.run_config failureSlot failureSlot_injective
    (HierarchyFixedWord.raw failureBits) (fun _ => 0) data _ _ base hb
  have hi : RecoveryFocus.config failureSlot (fun _ => 0) data
      (HierarchyFixedWord.cfg failureBits 0 (by omega)) = initialConfiguration failureMachine data := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick failureSlot i <;>
        simp [RecoveryFocus.config,hp,HierarchyFixedWord.cfg,initialConfiguration]
    · funext i
      cases hp : RecoveryFocus.pick failureSlot i with
      | none => simp [RecoveryFocus.config,hp,initialConfiguration]
      | some j =>
        have he : (1 : Fin 6)=i := RecoveryFocus.slot_of_pick failureSlot hp
        subst i
        simp [RecoveryFocus.config,hp,HierarchyFixedWord.cfg,initialConfiguration,hblank]
  rw [hi] at hr
  refine ⟨result,hr,?_⟩
  rw [hrt,hf]
  change (RecoveryFocus.config failureSlot (fun _ => 0) data
    (HierarchyFixedWord.cfg failureBits failureBits.length (by omega))).tapes (failureSlot 0)=failureBits
  simp [RecoveryFocus.config,RecoveryFocus.pick_slot failureSlot failureSlot_injective,HierarchyFixedWord.cfg]

end NearCubicGates.Adapters.Machine.Capped.ResultWriter
