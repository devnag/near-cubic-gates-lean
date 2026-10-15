import Proof.Circuits.DecompositionCountReady

/-! Cold original framed input through both header readers and actual child
and integer loop drivers. The original and raw source are retained. -/
namespace NearCubicWires.RepairOrdinary.DecompositionInputDrivers
open LocalBitMultitape RecoveryRootRound DecompositionInputCounts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 14) : Fin 35 :=
  if j=0 then 12 else if j=1 then 22 else ⟨j.val+21,by omega⟩
theorem slots_injective : Function.Injective slots := by decide
def fresh (j : Fin 14) : Fin 12 := ⟨j.val-2,by
  have hj := j.isLt
  omega⟩
theorem slots_fresh (j : Fin 14) (h0 : j≠0) (h1 : j≠1) :
    slots j=(fresh j).natAdd 23 := by
  apply Fin.ext
  have hj0 : j.val≠0 := fun he => h0 (Fin.ext he)
  have hj1 : j.val≠1 := fun he => h1 (Fin.ext he)
  simp only [slots,h0,h1,ite_false,Fin.val_mk,Fin.val_natAdd,fresh]
  omega
def input (a m : ℕ) (tail : List Bool) : Fin 35 → List Bool :=
  Fin.addCases (m:=23) (n:=12) (DecompositionInputCounts.input a m tail) (fun _ => [])
noncomputable def first := TapeEmbedding.machine 12 DecompositionInputCounts.machine
noncomputable def driver := RecoveryFocus.machine slots DecompositionCountReady.machine
noncomputable def machine := Composition.machine first driver
def budget (a m : ℕ) (tail : List Bool) :=
  DecompositionInputCounts.budget a m tail+1+DecompositionCountReady.budget a m

theorem drivers_run (a m : ℕ) (tail : List Bool) :
    ∃ r,run machine (budget a m tail) (input a m tail)=some r ∧
      r.final.tapes 0=frame (word a m tail) ∧ r.final.heads 0=0 ∧
      r.final.tapes 1=word a m tail ∧
      r.final.heads 1=(RepairRepresentation.natWord a++RepairRepresentation.natWord m).length ∧
      (∀ j,r.final.tapes (slots j)=DecompositionCountDrivers.output a m j) ∧
      (∀ j,r.final.heads (slots j)=DecompositionCountPosition.loopHeads j) ∧
      r.steps ≤ budget a m tail := by
  obtain ⟨base,hb,b0,bh0,b1,bh1,b12,bh12,b22,bh22,bs⟩ := DecompositionInputCounts.counts_run a m tail
  let prep := TapeEmbedding.receipt (fun _ : Fin 12 => 0) (fun _ : Fin 12 => []) base
  have hp := TapeEmbedding.run_embed DecompositionInputCounts.machine
    (fun _ : Fin 12 => 0) (fun _ : Fin 12 => []) _ _ base hb
  have pt (j : Fin 14) : prep.final.tapes (slots j)=DecompositionCountDrivers.input a m j := by
    by_cases h0 : j=0
    · subst j; exact b12
    by_cases h1 : j=1
    · subst j; exact b22
    rw [slots_fresh j h0 h1]
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_right]
    have hv0 : j.val≠0 := fun he => h0 (Fin.ext he)
    have hv1 : j.val≠1 := fun he => h1 (Fin.ext he)
    simp only [DecompositionCountDrivers.input,hv0,hv1,ite_false]
  have ph (j : Fin 14) : prep.final.heads (slots j)=DecompositionCountPosition.nativeHeads j := by
    by_cases h0 : j=0
    · subst j; exact bh12
    by_cases h1 : j=1
    · subst j; exact bh22
    rw [slots_fresh j h0 h1]
    simp only [prep,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_right,
      DecompositionCountPosition.nativeHeads,h0,h1,false_or,ite_false]
  obtain ⟨body,hlocal,lh,lt,ls⟩ := DecompositionCountReady.counts_run a m
  obtain ⟨called,hcall,cf,cs⟩ := RecoveryFocus.run_config slots slots_injective
    DecompositionCountReady.machine prep.final.heads prep.final.tapes _ _ body hlocal
  have he : RecoveryFocus.config slots prep.final.heads prep.final.tapes (DecompositionCountReady.entry a m)=
      Composition.restart prep.final driver.start := by
    apply configuration_ext
    · rfl
    · funext i
      cases hi : RecoveryFocus.pick slots i with
      | none => simp only [RecoveryFocus.config,hi,Composition.restart]
      | some j =>
        have hj := RecoveryFocus.slot_of_pick slots hi
        simp only [RecoveryFocus.config,hi,DecompositionCountReady.entry,Composition.restart]
        exact (ph j).symm.trans (congrArg prep.final.heads hj)
    · exact install_existing slots prep.final.tapes (DecompositionCountDrivers.input a m) pt
  rw [he] at hcall
  have whole := Composition.run_join first driver _ _ _ prep called hp hcall
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 12 => 0)
      (fun _ : Fin 12 => []) (initialConfiguration DecompositionInputCounts.machine
        (DecompositionInputCounts.input a m tail)))=initialConfiguration machine (input a m tail) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=23) (n:=12) (fun j => ?_) (fun j => ?_) i
      · simp only [Composition.leftConfig,TapeEmbedding.config,Fin.addCases_left,initialConfiguration]
      · simp only [Composition.leftConfig,TapeEmbedding.config,Fin.addCases_right,initialConfiguration]
    · rfl
  rw [hin] at whole
  have other (i : Fin 35) (hi : RecoveryFocus.pick slots i=none) :
      called.final.tapes i=prep.final.tapes i ∧ called.final.heads i=prep.final.heads i := by
    rw [cf]
    simp only [RecoveryFocus.config,hi,and_self]
  refine ⟨Composition.joinedReceipt prep called,whole,?_,?_,?_,?_,?_,?_,?_⟩
  · change called.final.tapes 0=_
    exact ((other 0 (by decide)).1).trans b0
  · change called.final.heads 0=_
    exact ((other 0 (by decide)).2).trans bh0
  · change called.final.tapes 1=_
    exact ((other 1 (by decide)).1).trans b1
  · change called.final.heads 1=_
    exact ((other 1 (by decide)).2).trans bh1
  · intro j
    change called.final.tapes (slots j)=_
    rw [cf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,lt]
  · intro j
    change called.final.heads (slots j)=_
    rw [cf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,lh]
  · change base.steps+1+called.steps ≤ _
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.DecompositionInputDrivers
