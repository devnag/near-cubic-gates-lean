import Proof.MachineModel.UInitializationLayout

/-! Actual key construction followed by both chronological initialization
scans. The global output is appended once and the serial counter is retained
for the subsequent transition walk. -/
namespace NearCubicWires.RepairOrdinary.UInitialization
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (w n B : ℕ) : ℕ := 131*(n+B+1)*(w+1)

theorem producer_run (L w : ℕ) (input witness : List Bool)
    (hL : 2≤L) (hn : input.length≤witness.length) (hB : witness.length≤L) (hw : 4*L+4≤2^w) :
    ∃ r, ∃ small : Configuration 11 154,run machine (budget w input.length witness.length) (tapes w input witness)=some r ∧
      r.steps≤budget w input.length witness.length ∧
      r.final.heads=(RecoveryFocus.config memorySlots (fun _ : Fin 21 => 0) (afterKey w input witness) small).heads ∧
      r.final.tapes=(RecoveryFocus.config memorySlots (fun _ : Fin 21 => 0) (afterKey w input witness) small).tapes ∧
      r.final.tapes 16=MemoryInitialEmission.fields (2*w) (2*w+2) w 0
        (MemoryInitialization.events input witness) ∧
      ZeroPadding.config (MemoryInitializationCarrier.capacities w) small=
        MemoryInitialSources.config 153 (2*w) (2*w+2) ((frame input).length+(frame witness).length)
          (frame input).length (2^w+(frame witness).length) (4*w+5)
          (MemoryInitialEmission.fields (2*w) (2*w+2) w 0 (MemoryInitialization.events input witness))
          (frame input) (frame witness) (frame input).length (frame witness).length false := by
  obtain ⟨first,hfirst,hft,hfh,hfs⟩ := key_run w input witness
  obtain ⟨last,small,hlast,hlf,hevents,hsmall⟩ := memory_run L w input witness hL hn hB hw
  have hre : Composition.restart first.final memoryProgram.start=
      initialConfiguration memoryProgram (afterKey w input witness) := by
    apply configuration_ext
    · rfl
    · exact funext hfh
    · exact hft
  change runFrom memoryProgram (MemoryInitializationCarrier.budget w input.length witness.length)
    (initialConfiguration memoryProgram (afterKey w input witness))=some last at hlast
  rw [←hre] at hlast
  have hjoin := Composition.run_join keyProgram memoryProgram (50*(w+1))
    (MemoryInitializationCarrier.budget w input.length witness.length)
    (initialConfiguration keyProgram (tapes w input witness)) first last hfirst hlast
  let r := Composition.joinedReceipt first last
  have hb : 50*(w+1)+1+MemoryInitializationCarrier.budget w input.length witness.length≤
      budget w input.length witness.length := by
    dsimp [budget,MemoryInitializationCarrier.budget]
    nlinarith
  have hmore := runFrom_moreFuel machine (50*(w+1)+1+MemoryInitializationCarrier.budget w input.length witness.length)
    (budget w input.length witness.length-(50*(w+1)+1+MemoryInitializationCarrier.budget w input.length witness.length))
    _ r hjoin
  rw [Nat.add_sub_of_le hb] at hmore
  have hs := runFrom_steps_le machine _ _ r hmore
  refine ⟨r,small,hmore,hs,?_,?_,?_,hsmall⟩
  · simpa only [r,Composition.joinedReceipt,Composition.rightConfig] using congrArg Configuration.heads hlf
  · simpa only [r,Composition.joinedReceipt,Composition.rightConfig] using congrArg Configuration.tapes hlf
  · exact hevents

end NearCubicWires.RepairOrdinary.UInitialization
