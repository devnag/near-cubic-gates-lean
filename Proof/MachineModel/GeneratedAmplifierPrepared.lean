import Proof.MachineModel.GeneratedAmplifierCopies
import Proof.MachineModel.GeneratedAmplifierArity

/-! The actual external prefix leaves the table start, whole-input end and
computed unary arity on fixed tapes for the address reader. -/
namespace NearCubicWires.RepairOrdinary.GeneratedAmplifier.Prepared
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 9→Fin 13 := ![3,5,6,7,8,9,10,11,12]
noncomputable def copies := TapeEmbedding.machine 8 Copies.machine
noncomputable def arity := RecoveryFocus.machine slots Arity.machine
noncomputable def machine := Composition.machine copies arity
def input (word : List Bool) : Fin 13→List Bool := fun i => if i=0 then frame word else []
def budget (n : ℕ) (tail : List Bool) := 8*(frame n.bits++tail).length+8+Arity.budget n

theorem prepared_run (n : ℕ) (tail : List Bool) :
    let word := frame n.bits++tail
    ∃ r,run machine (budget n tail) (input word)=some r ∧ r.steps≤budget n tail ∧
      r.final.tapes 1=word ∧ r.final.heads 1=word.length ∧
      r.final.tapes 3=word ∧ r.final.heads 3=2*n.bits.length+1 ∧
      r.final.tapes 12=UnaryTemplate.tape n ∧ r.final.heads 12=1 := by
  dsimp only
  let word := frame n.bits++tail
  obtain ⟨base,hb,hf,hs⟩ := Copies.copies_run word
  have he := TapeEmbedding.run_embed Copies.machine (fun _ : Fin 8 => 0) (fun _ : Fin 8 => []) _ _ base hb
  let ambient := TapeEmbedding.config (fun _ : Fin 8 => 0) (fun _ : Fin 8 => []) base.final
  obtain ⟨last,hl,hls,hsource,hsourceHead,hcount,hcountHead⟩ := Arity.arity_run n tail
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) Arity.machine
    ambient.heads ambient.tapes _ _ last hl
  have hi : RecoveryFocus.config slots ambient.heads ambient.tapes
      (initialConfiguration Arity.machine (Arity.input word))=Composition.restart ambient arity.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      dsimp only [ambient]
      rw [hf]
      fin_cases i <;> simp [slots,TapeEmbedding.config,Copies.finished,initialConfiguration,Fin.addCases]
    · intro i
      dsimp only [ambient]
      rw [hf]
      fin_cases i <;> simp [slots,TapeEmbedding.config,Copies.finished,initialConfiguration,Arity.input,Fin.addCases]
  rw [hi] at hfocus
  have hj := Composition.run_join copies arity _ _ _
    (TapeEmbedding.receipt (fun _ : Fin 8 => 0) (fun _ : Fin 8 => []) base) focused he hfocus
  have hentry : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 8 => 0) (fun _ : Fin 8 => [])
      (initialConfiguration Copies.machine (Copies.input word)))=initialConfiguration machine (input word) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hentry] at hj
  have htime : (8*word.length+7)+1+Arity.budget n=budget n tail := by unfold budget word; omega
  rw [htime] at hj
  have hn : RecoveryFocus.pick slots (1 : Fin 13)=none := by decide
  have hother : focused.final.tapes 1=word ∧ focused.final.heads 1=word.length := by
    simp only [hff,RecoveryFocus.config,hn]
    dsimp only [ambient]
    rw [hf]
    simp [TapeEmbedding.config,Copies.finished,Fin.addCases]
  have htape (i : Fin 9) : focused.final.tapes (slots i)=last.final.tapes i := by
    simp only [hff,RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
  have hhead (i : Fin 9) : focused.final.heads (slots i)=last.final.heads i := by
    simp only [hff,RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
  refine ⟨Composition.joinedReceipt
    (TapeEmbedding.receipt (fun _ : Fin 8 => 0) (fun _ : Fin 8 => []) base) focused,hj,?_,hother.1,hother.2,
    (htape 0).trans hsource,(hhead 0).trans hsourceHead,(htape 8).trans hcount,(hhead 8).trans hcountHead⟩
  change base.steps+1+focused.steps≤_
  rw [hs,hfs,←htime]
  omega

end NearCubicWires.RepairOrdinary.GeneratedAmplifier.Prepared
