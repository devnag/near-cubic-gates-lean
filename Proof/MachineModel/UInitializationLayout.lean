import Proof.Amplification.RecoveryReadyCalls
import Proof.MachineModel.ClockInitialKey
import Proof.MachineModel.OrdinaryMemoryInitializationCarrier

/-! Initialization has five physical inputs: unary w/I/K and the two framed
source words. This layout supplies the remaining tape-one key by the actual
paid producer, retaining every source until its initialization scan. -/
namespace NearCubicWires.RepairOrdinary.UInitialization
open LocalBitMultitape ClockJoin RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (w : ℕ) (input witness : List Bool) : Fin 9 → List Bool :=
  ![List.replicate (2*w) true,frame input,frame witness,[],[],[],[],[],[]]
def tapes (w : ℕ) (input witness : List Bool) : Fin 21 → List Bool :=
  fun i => Fin.addCases (ClockInitialKey.input w) (extra w input witness) i

def afterKey (w : ℕ) (input witness : List Bool) : Fin 21 → List Bool :=
  fun i => Fin.addCases (ClockInitialKey.output w) (extra w input witness) i

def memorySlots : Fin 11 → Fin 21 := ![15,12,16,17,18,6,19,20,13,14,10]
theorem memory_injective : Function.Injective memorySlots := by decide
noncomputable def keyProgram : Machine 21 25 := TapeEmbedding.machine 9 ClockInitialKey.machine
noncomputable def memoryProgram : Machine 21 154 := RecoveryFocus.machine memorySlots MemoryInitialSources.machine
noncomputable def machine : Machine 21 179 := Composition.machine keyProgram memoryProgram

theorem key_run (w : ℕ) (input witness : List Bool) :
    ∃ r,run keyProgram (50*(w+1)) (tapes w input witness)=some r ∧
      r.final.tapes=afterKey w input witness ∧ (∀ i,r.final.heads i=0) ∧ r.steps≤50*(w+1) := by
  obtain ⟨base,hb,ht,hh,hs⟩ := ClockInitialKey.key_ready w
  have he := TapeEmbedding.run_embed ClockInitialKey.machine (fun _ : Fin 9 => 0)
    (extra w input witness) _ _ base hb
  let r := TapeEmbedding.receipt (fun _ : Fin 9 => 0) (extra w input witness) base
  have hi : TapeEmbedding.config (fun _ : Fin 9 => 0) (extra w input witness)
      (initialConfiguration ClockInitialKey.machine (ClockInitialKey.input w))=
      initialConfiguration keyProgram (tapes w input witness) := by
    apply configuration_ext
    · rfl
    · funext i; simp [TapeEmbedding.config,initialConfiguration,Fin.addCases]
    · rfl
  rw [hi] at he
  refine ⟨r,he,?_,?_,hs⟩
  · change (fun i : Fin 21 => Fin.addCases (motive:=fun _ => List Bool) base.final.tapes (extra w input witness) i)=_
    rw [ht]
    rfl
  · intro i
    simp [r,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,hh]

theorem memory_entry (w : ℕ) (input witness : List Bool) (j : Fin 11) :
    afterKey w input witness (memorySlots j)=MemoryInitializationCarrier.tapes w input witness j := by
  fin_cases j <;> simp [afterKey,memorySlots,ClockInitialKey.output,extra,
    Fin.addCases,MemoryInitializationCarrier.tapes,ClockInitialKey.key_binary,ClockInitialKey.K]

theorem memory_input_eq (w : ℕ) (input witness : List Bool) :
    RecoveryFocus.config memorySlots (fun _ : Fin 21 => 0) (afterKey w input witness)
      (initialConfiguration MemoryInitialSources.machine (MemoryInitializationCarrier.tapes w input witness))=
      initialConfiguration memoryProgram (afterKey w input witness) := by
  apply configuration_ext
  · rfl
  · funext i
    cases hp : RecoveryFocus.pick memorySlots i <;> simp [RecoveryFocus.config,hp,initialConfiguration]
  · exact install_existing memorySlots _ _ (memory_entry w input witness)

theorem memory_run (L w : ℕ) (input witness : List Bool)
    (hL : 2≤L) (hn : input.length≤witness.length) (hB : witness.length≤L) (hw : 4*L+4≤2^w) :
    ∃ r small,run memoryProgram (MemoryInitializationCarrier.budget w input.length witness.length)
        (afterKey w input witness)=some r ∧
      r.final=RecoveryFocus.config memorySlots (fun _ : Fin 21 => 0) (afterKey w input witness) small ∧
      r.final.tapes 16=MemoryInitialEmission.fields (2*w) (2*w+2) w 0
        (MemoryInitialization.events input witness) ∧
      ZeroPadding.config (MemoryInitializationCarrier.capacities w) small=
        MemoryInitialSources.config 153 (2*w) (2*w+2) ((frame input).length+(frame witness).length)
          (frame input).length (2^w+(frame witness).length) (4*w+5)
          (MemoryInitialEmission.fields (2*w) (2*w+2) w 0 (MemoryInitialization.events input witness))
          (frame input) (frame witness) (frame input).length (frame witness).length false := by
  obtain ⟨base,hb,hout,hfinal⟩ := MemoryInitializationCarrier.initialized_run L w input witness hL hn hB hw
  obtain ⟨r,hr,hf,_⟩ := RecoveryFocus.run_config memorySlots memory_injective MemoryInitialSources.machine
    (fun _ : Fin 21 => 0) (afterKey w input witness) _ _ base hb
  rw [memory_input_eq] at hr
  refine ⟨r,base.final,hr,hf,?_,hfinal⟩
  change r.final.tapes (memorySlots 2)=_
  simp [hf,RecoveryFocus.config,RecoveryFocus.pick_slot _ memory_injective,hout]

end NearCubicWires.RepairOrdinary.UInitialization
