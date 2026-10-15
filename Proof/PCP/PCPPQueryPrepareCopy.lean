import Proof.PCP.PCPPQueryNatural
import Proof.PCP.PCPPQuerySupport

/-! The cold query prefix physically isolates the source constructor input,
then loads a separate raw copy for the arity reader. The original isolated
frame remains at head zero for the source call. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryPrepareCopy
open LocalBitMultitape RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 3→Fin 27 := ![3,5,6]
noncomputable def entryProgram : Machine 27 10 := TapeEmbedding.machine 22 PCPPQueryInput.machine
noncomputable def copy : Machine 27 5 := RecoveryFocus.machine slots Streaming.machine
noncomputable def machine := Composition.machine entryProgram copy
def input (word : List Bool) : Fin 27→List Bool := fun i => if i=0 then frame word else []
def budget (bits tail : List Bool) := PCPPQueryInput.budget bits tail+4*bits.length+3
def heads (bits : List Bool) : Fin 27→ℕ := fun i => if i=1 then 2*bits.length+1 else 0
def tapes (bits tail : List Bool) : Fin 27→List Bool := fun i =>
  if i=0 then frame (frame bits++tail) else if i=1 then frame bits++tail
  else if i=2 then List.replicate (frame bits++tail).length false
  else if i=3 then frame bits else if i=4 then List.replicate (2*bits.length+1) false
  else if i=5 then bits else if i=6 then List.replicate bits.length false else []
def output (bits tail : List Bool) : Configuration 27 15 := ⟨14,heads bits,tapes bits tail⟩

theorem copy_run (bits tail : List Bool) :
    ∃ r,run machine (budget bits tail) (input (frame bits++tail))=some r ∧
      r.final=output bits tail ∧ r.steps=budget bits tail := by
  obtain ⟨first,hfirst,hff,hfs⟩ := PCPPQueryInput.input_run bits tail
  have ha := TapeEmbedding.run_embed PCPPQueryInput.machine (fun _ : Fin 22 => 0)
    (fun _ : Fin 22 => []) _ _ first hfirst
  rw [StreamPrepare.embed_initial] at ha
  let ambient := TapeEmbedding.config (fun _ : Fin 22 => 0) (fun _ : Fin 22 => []) first.final
  obtain ⟨last,hl,hlf,hls,_⟩ := Streaming.copy_run bits
  obtain ⟨focused,hfocus,hfocused,hsteps⟩ := RecoveryFocus.run_config slots (by decide)
    Streaming.machine ambient.heads ambient.tapes _ _ last hl
  have hi : RecoveryFocus.config slots ambient.heads ambient.tapes
      (initialConfiguration Streaming.machine (fun i => if i.val=0 then frame bits else []))=
      Composition.restart ambient copy.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      dsimp only [ambient]
      rw [hff]
      fin_cases i <;> simp [initialConfiguration,TapeEmbedding.config,PCPPQueryInput.output,slots,Fin.addCases]
    · intro i
      dsimp only [ambient]
      rw [hff]
      fin_cases i <;> simp [initialConfiguration,TapeEmbedding.config,PCPPQueryInput.output,slots,Fin.addCases]
  rw [hi] at hfocus
  have hj := Composition.run_join entryProgram copy (PCPPQueryInput.budget bits tail) (4*bits.length+2) _
    (TapeEmbedding.receipt (fun _ : Fin 22 => 0) (fun _ : Fin 22 => []) first) focused ha hfocus
  have htime : PCPPQueryInput.budget bits tail+1+(4*bits.length+2)=budget bits tail := by unfold budget; omega
  rw [htime] at hj
  have he : Composition.leftConfig 5
      (initialConfiguration (TapeEmbedding.machine 22 PCPPQueryInput.machine)
        (Fin.addCases (motive:=fun _ : Fin (5+22) => List Bool)
          (PCPPQueryInput.input (frame bits++tail)) (fun _ : Fin 22 => [])))=
      initialConfiguration machine (input (frame bits++tail)) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [he] at hj
  have hpick (i : Fin 27) : RecoveryFocus.pick slots i=
      if i=3 then some 0 else if i=5 then some 1 else if i=6 then some 2 else none := by
    by_cases h3 : i=3
    · subst i; exact RecoveryFocus.pick_slot slots (by decide) 0
    by_cases h5 : i=5
    · subst i; exact RecoveryFocus.pick_slot slots (by decide) 1
    by_cases h6 : i=6
    · subst i; exact RecoveryFocus.pick_slot slots (by decide) 2
    have hn : ¬∃ j,slots j=i := by
      rintro ⟨j,hj⟩
      fin_cases j <;> simp [slots] at hj <;> omega
    simp [RecoveryFocus.pick,hn,h3,h5,h6]
  refine ⟨Composition.joinedReceipt
    (TapeEmbedding.receipt (fun _ : Fin 22 => 0) (fun _ : Fin 22 => []) first) focused,hj,?_,?_⟩
  · change Composition.rightConfig 10 focused.final=_
    rw [hfocused,hlf]
    dsimp only [ambient]
    rw [hff]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [Composition.rightConfig,RecoveryFocus.config,hpick,
        TapeEmbedding.config,PCPPQueryInput.output,Streaming.finished,Streaming.config,Fin.addCases,output,heads]
    · funext i; fin_cases i <;> simp [Composition.rightConfig,RecoveryFocus.config,hpick,
        TapeEmbedding.config,PCPPQueryInput.output,Streaming.finished,Streaming.config,Fin.addCases,output,tapes]
  · change first.steps+1+focused.steps=_
    rw [hfs,hsteps,hls]
    exact htime

end NearCubicWires.RepairOrdinary.PCPPQueryPrepareCopy
