import Proof.MachineModel.GeneratedAmplifierCopyReady
import Proof.MachineModel.OrdinaryWilliamsSourceCropLayout

/-! Two cold physical views of the complete logical input: one retains its
append cursor, while the other starts at zero for header parsing. -/
namespace NearCubicWires.RepairOrdinary.GeneratedAmplifier.Copies
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def first := TapeEmbedding.machine 2 Copy.sourceReset
def slots : Fin 3→Fin 5 := ![0,3,4]
noncomputable def second := RecoveryFocus.machine slots Streaming.machine
noncomputable def machine := Composition.machine first second
def input (word : List Bool) : Fin 5→List Bool := fun i => if i=0 then frame word else []
def finished (word : List Bool) : Configuration 5 10 :=
  ⟨9,![0,word.length,0,0,0],![frame word,word,List.replicate (2*word.length+1) false,
    word,List.replicate word.length false]⟩

theorem copies_run (word : List Bool) :
    ∃ r,run machine (8*word.length+7) (input word)=some r ∧
      r.final=finished word ∧ r.steps=8*word.length+7 := by
  obtain ⟨base,hb,hf,hs⟩ := Copy.source_reset_run word
  have he := TapeEmbedding.run_embed Copy.sourceReset (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) _ _ base hb
  let ambient := TapeEmbedding.config (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) base.final
  obtain ⟨last,hl,hlf,hls,_⟩ := Streaming.copy_run word
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) Streaming.machine
    ambient.heads ambient.tapes _ _ last hl
  have hi : RecoveryFocus.config slots ambient.heads ambient.tapes
      (initialConfiguration Streaming.machine (fun i => if i.val=0 then frame word else []))=
      Composition.restart ambient second.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      dsimp only [ambient]
      rw [hf]
      fin_cases i <;> simp [slots,TapeEmbedding.config,Copy.endCopy,initialConfiguration,Fin.addCases]
    · intro i
      dsimp only [ambient]
      rw [hf]
      fin_cases i <;> simp [slots,TapeEmbedding.config,Copy.endCopy,initialConfiguration,Fin.addCases]
  rw [hi] at hfocus
  have hj := Composition.run_join first second _ _ _
    (TapeEmbedding.receipt (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) base) focused he hfocus
  have htime : (4*word.length+4)+1+(4*word.length+2)=8*word.length+7 := by omega
  rw [htime] at hj
  have hentry : Composition.leftConfig 5 (TapeEmbedding.config (fun _ : Fin 2 => 0) (fun _ : Fin 2 => [])
      (initialConfiguration Copy.sourceReset ![frame word,[],[]]))=initialConfiguration machine (input word) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hentry] at hj
  have hpick : ∀ i : Fin 5,RecoveryFocus.pick slots i=(![some 0,none,none,some 1,some 2] : Fin 5→Option (Fin 3)) i := by
    intro i; fin_cases i
    · exact RecoveryFocus.pick_slot slots (by decide) 0
    · decide
    · decide
    · exact RecoveryFocus.pick_slot slots (by decide) 1
    · exact RecoveryFocus.pick_slot slots (by decide) 2
  refine ⟨Composition.joinedReceipt
    (TapeEmbedding.receipt (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) base) focused,hj,?_,?_⟩
  · change Composition.rightConfig 5 focused.final=_
    rw [hff,hlf]
    dsimp only [ambient]
    rw [hf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [Composition.rightConfig,RecoveryFocus.config,hpick,
        TapeEmbedding.config,Copy.endCopy,Streaming.finished,Streaming.config,finished,Fin.addCases]
    · funext i; fin_cases i <;> simp [Composition.rightConfig,RecoveryFocus.config,hpick,
        TapeEmbedding.config,Copy.endCopy,Streaming.finished,Streaming.config,finished,Fin.addCases]
  · change base.steps+1+focused.steps=_
    rw [hs,hfs,hls]
    exact htime

end NearCubicWires.RepairOrdinary.GeneratedAmplifier.Copies
