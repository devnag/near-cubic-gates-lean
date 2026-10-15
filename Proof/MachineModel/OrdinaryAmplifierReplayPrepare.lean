import Proof.MachineModel.OrdinaryAmplifierReplayFrame
import Proof.MachineModel.GeneratedAmplifierArity
import Proof.MachineModel.OrdinaryMatrixTemplateCopy
import Proof.MachineModel.OrdinaryMatrixScorePower

/-! The actual raw arity header supplies the exact table-length driver.
All preparation starts with one raw payload and blank fixed workspace. -/
namespace NearCubicWires.RepairOrdinary.AmplifierReplay.Prepare
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def input (word : List Bool) : Fin 28→List Bool := fun i => if i=0 then word else []
def arity := TapeEmbedding.machine 18 (Rewind.machine GeneratedAmplifier.Arity.machine)
def copySlots : Fin 5→Fin 28 := ![8,10,11,12,13]
def copy := RecoveryFocus.machine copySlots MatrixTemplateCopy.resetMachine
def copied :=  Composition.machine arity copy
def powerSlots : Fin 14→Fin 28 := ![10,14,15,16,17,18,19,20,21,22,23,24,25,26]
def power := RecoveryFocus.machine powerSlots MatrixScorePower.machine
def machine := Composition.machine copied power
def arityBudget (n : ℕ) := 2*GeneratedAmplifier.Arity.budget n+2
def prefixBudget (n : ℕ) := arityBudget n+1+(4*n+12)
def budget (n : ℕ) := prefixBudget n+1+MatrixScorePower.budget n

theorem arity_run (n : ℕ) (tail : List Bool) :
    ∃ r,run arity (arityBudget n) (input (frame n.bits++tail))=some r ∧
      r.final.tapes 0=frame n.bits++tail ∧ r.final.tapes 8=UnaryTemplate.tape n ∧
      (∀ i,r.final.heads i=0) ∧ (∀ i,10 ≤ i.val → r.final.tapes i=[]) ∧ r.steps ≤ arityBudget n := by
  obtain ⟨base,hb,hbs,h0,_h0,h8,_h8⟩ := GeneratedAmplifier.Arity.arity_run n tail
  obtain ⟨last,hl,ht,hh,hs,_⟩ := Rewind.reset_run GeneratedAmplifier.Arity.machine _ _ base hb
  have hbound : 2*base.steps+2 ≤ arityBudget n := by unfold arityBudget; omega
  have hm := run_moreFuel (Rewind.machine GeneratedAmplifier.Arity.machine)
    (2*base.steps+2) (arityBudget n-(2*base.steps+2)) _ last hl
  rw [Nat.add_sub_of_le hbound] at hm
  have he := TapeEmbedding.run_embed (Rewind.machine GeneratedAmplifier.Arity.machine)
    (fun _ : Fin 18 => 0) (fun _ : Fin 18 => []) _ _ last hm
  let result := TapeEmbedding.receipt (fun _ : Fin 18 => 0) (fun _ : Fin 18 => []) last
  have hi : TapeEmbedding.config (fun _ : Fin 18 => 0) (fun _ : Fin 18 => [])
      (initialConfiguration (Rewind.machine GeneratedAmplifier.Arity.machine)
        (Fin.addCases (motive:=fun _ : Fin (9+1) => List Bool)
          (GeneratedAmplifier.Arity.input (frame n.bits++tail)) (fun _ : Fin 1 => [])))=
      initialConfiguration arity (input (frame n.bits++tail)) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at he
  refine ⟨result,he,(ht 0).trans h0,(ht 8).trans h8,?_,?_,?_⟩
  · intro i
    refine Fin.addCases (m:=10) (n:=18) (fun j => ?_) (fun j => ?_) i
    · simpa only [result,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left] using hh j
    · simp only [result,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_right]
  · intro i hi
    revert hi
    refine Fin.addCases (m:=10) (n:=18) (fun j => ?_) (fun j => ?_) i
    · intro hj; simp only [Fin.val_castAdd] at hj; omega
    · intro _; simp only [result,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_right]
  · change last.steps ≤ _
    omega

theorem prefix_run (n : ℕ) (tail : List Bool) :
    ∃ r,run copied (prefixBudget n) (input (frame n.bits++tail))=some r ∧
      r.final.tapes 0=frame n.bits++tail ∧ r.final.tapes 10=List.replicate n true ∧
      (∀ i,r.final.heads i=0) ∧ (∀ i,14 ≤ i.val → r.final.tapes i=[]) ∧ r.steps ≤ prefixBudget n := by
  obtain ⟨base,hb,h0,h8,hh,hblank,hsteps⟩ := arity_run n tail
  obtain ⟨localRun,hl,_lt0,lt1,_lt2,_lt3,lh,ls⟩ := MatrixTemplateCopy.reset_run n
  have hi : RecoveryFocus.config copySlots base.final.heads base.final.tapes
      (initialConfiguration MatrixTemplateCopy.resetMachine (MatrixTemplateCopy.resetInput n))=
      Composition.restart base.final copy.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; simp [hh,initialConfiguration]
    · intro i; fin_cases i
      · exact h8
      · exact hblank 10 (by decide)
      · exact hblank 11 (by decide)
      · exact hblank 12 (by decide)
      · exact hblank 13 (by decide)
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config copySlots (by decide)
    MatrixTemplateCopy.resetMachine base.final.heads base.final.tapes _ _ localRun hl
  rw [hi] at hf
  have hj := Composition.run_join arity copy _ _ _ base focused hb hf
  refine ⟨Composition.joinedReceipt base focused,hj,?_,?_,?_,?_,?_⟩
  · change focused.final.tapes 0=_
    rw [hff]
    simpa only [RecoveryFocus.config,show RecoveryFocus.pick copySlots 0=none by decide] using h0
  · change focused.final.tapes (copySlots 1)=_
    rw [hff]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot copySlots (by decide)] using lt1
  · intro i
    change focused.final.heads i=0
    rw [hff]
    cases h : RecoveryFocus.pick copySlots i <;> simp [RecoveryFocus.config,h,hh,lh]
  · intro i hi
    change focused.final.tapes i=[]
    rw [hff]
    have hp : RecoveryFocus.pick copySlots i=none := by
      fin_cases i <;> simp at hi
      all_goals decide
    simpa only [RecoveryFocus.config,hp] using hblank i (by omega)
  · change base.steps+1+focused.steps ≤ _
    rw [hfs,ls]
    unfold prefixBudget
    omega

theorem prepare_run (n : ℕ) (tail : List Bool) :
    ∃ r,run machine (budget n) (input (frame n.bits++tail))=some r ∧
      r.final.tapes 0=frame n.bits++tail ∧ r.final.heads 0=0 ∧
      r.final.tapes 26=UnaryTemplate.tape (2^n) ∧ r.final.heads 26=1 ∧
      r.final.tapes 27=[] ∧ r.final.heads 27=0 ∧ r.steps ≤ budget n := by
  obtain ⟨base,hb,h0,h10,hh,hblank,hsteps⟩ := prefix_run n tail
  obtain ⟨localRun,hl,_l0,_l2,_l6,l13,lh13,lh,ls⟩ := MatrixScorePower.power_run n
  have hi : RecoveryFocus.config powerSlots base.final.heads base.final.tapes
      (initialConfiguration MatrixScorePower.machine (MatrixScorePower.input n))=
      Composition.restart base.final power.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; simp [hh,initialConfiguration]
    · intro i; fin_cases i
      · exact h10
      all_goals exact hblank _ (by decide)
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config powerSlots (by decide)
    MatrixScorePower.machine base.final.heads base.final.tapes _ _ localRun hl
  rw [hi] at hf
  have hj := Composition.run_join copied power _ _ _ base focused hb hf
  have hp0 : RecoveryFocus.pick powerSlots 0=none := by decide
  have hp27 : RecoveryFocus.pick powerSlots 27=none := by decide
  refine ⟨Composition.joinedReceipt base focused,hj,?_,?_,?_,?_,?_,?_,?_⟩
  · change focused.final.tapes 0=_
    rw [hff]
    simpa only [RecoveryFocus.config,hp0] using h0
  · change focused.final.heads 0=0
    simp only [hff,RecoveryFocus.config,hp0,hh]
  · change focused.final.tapes (powerSlots 13)=_
    rw [hff]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot powerSlots (by decide)] using l13
  · change focused.final.heads (powerSlots 13)=1
    rw [hff]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot powerSlots (by decide)] using lh13
  · change focused.final.tapes 27=[]
    rw [hff]
    simpa only [RecoveryFocus.config,hp27] using hblank 27 (by decide)
  · change focused.final.heads 27=0
    simp only [hff,RecoveryFocus.config,hp27,hh]
  · change base.steps+1+focused.steps ≤ _
    rw [hfs]
    unfold budget
    omega

end
end NearCubicWires.RepairOrdinary.AmplifierReplay.Prepare
