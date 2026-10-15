import Proof.Circuits.DecompositionSourceCount

/-! Cold threshold input preparation retains the original source request,
physically decodes its arity, and starts the destination with its natWord. -/
namespace NearCubicWires.RepairOrdinary.DecompositionSource.Prepare
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem field_focus {u z : ℕ} (slots : Fin 3→Fin u) (hinj : Function.Injective slots)
    (ambient : Configuration u z) (n : ℕ) (pre tail backing out : List Bool)
    (ht : ∀ j,ambient.tapes (slots j)=(![pre++natWord n++tail,backing,out] : Fin 3→List Bool) j)
    (hh : ∀ j,ambient.heads (slots j)=(![pre.length,0,out.length] : Fin 3→ℕ) j) :
    ∃ r,runFrom (RecoveryFocus.machine slots (PCPPQueryField.machine true))
      (PCPPQueryField.fieldCost n)
      (Composition.restart ambient (RecoveryFocus.machine slots (PCPPQueryField.machine true)).start)=some r ∧
      r.steps=PCPPQueryField.fieldCost n ∧
      r.final.tapes (slots 0)=pre++natWord n++tail ∧
      r.final.heads (slots 0)=pre.length+(natWord n).length ∧
      r.final.tapes (slots 1)=PCPPQueryField.saved n backing ∧ r.final.heads (slots 1)=0 ∧
      r.final.tapes (slots 2)=out++natWord n ∧ r.final.heads (slots 2)=(out++natWord n).length ∧
      (∀ i,RecoveryFocus.pick slots i=none → r.final.tapes i=ambient.tapes i ∧ r.final.heads i=ambient.heads i) := by
  obtain ⟨base,hb,hbf,hbs⟩ := PCPPQueryField.nat_run true pre tail backing out n
  obtain ⟨r,hr,hf,hs⟩ := RecoveryFocus.run_config slots hinj (PCPPQueryField.machine true)
    ambient.heads ambient.tapes _ _ base hb
  have he : RecoveryFocus.config slots ambient.heads ambient.tapes
      (PCPPQueryField.cfg 0 (pre++natWord n++tail) pre.length backing 0 out)=
      Composition.restart ambient (RecoveryFocus.machine slots (PCPPQueryField.machine true)).start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; exact hh i
    · intro i; exact ht i
  rw [he] at hr
  have tape (j : Fin 3) : r.final.tapes (slots j)=base.final.tapes j := by
    simp only [hf,RecoveryFocus.config,RecoveryFocus.pick_slot slots hinj]
  have head (j : Fin 3) : r.final.heads (slots j)=base.final.heads j := by
    simp only [hf,RecoveryFocus.config,RecoveryFocus.pick_slot slots hinj]
  refine ⟨r,hr,hs.trans hbs,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [tape,hbf]; rfl
  · rw [head,hbf]; simp [PCPPQueryField.payload,PCPPQueryField.cfg]; omega
  · rw [tape,hbf]; rfl
  · rw [head,hbf]; rfl
  · rw [tape,hbf]; rfl
  · rw [head,hbf]; rfl
  · intro i hi; simp [hf,RecoveryFocus.config,hi]

def countSlots : Fin 12→Fin 16 := ![1,3,4,5,6,7,8,9,10,11,12,13]
def fieldSlots : Fin 3→Fin 16 := ![1,14,15]
def copy := TapeEmbedding.machine 13 Streaming.machine
noncomputable def count := RecoveryFocus.machine countSlots Count.machine
noncomputable def field := RecoveryFocus.machine fieldSlots (PCPPQueryField.machine true)
noncomputable def prefixMachine := Composition.machine copy count
noncomputable def machine := Composition.machine prefixMachine field
def input (n : ℕ) (tail : List Bool) : Fin 16→List Bool :=
  fun i => if i.val=0 then frame (natWord n++tail) else []
def budget (n : ℕ) (tail : List Bool) :=
  4*(natWord n++tail).length+Count.budget n+PCPPQueryField.fieldCost n+4

theorem prepare_run (n : ℕ) (tail : List Bool) :
    ∃ r,run machine (budget n tail) (input n tail)=some r ∧ r.steps ≤ budget n tail ∧
      r.final.tapes 0=frame (natWord n++tail) ∧ r.final.heads 0=0 ∧
      r.final.tapes 12=UnaryTemplate.tape n ∧ r.final.heads 12=1 ∧
      r.final.tapes 14=PCPPQueryField.saved n [] ∧ r.final.heads 14=0 ∧
      r.final.tapes 15=natWord n ∧ r.final.heads 15=(natWord n).length := by
  obtain ⟨base,hb,hbf,hbs,_⟩ := Streaming.copy_run (natWord n++tail)
  have he := TapeEmbedding.run_embed Streaming.machine (fun _ : Fin 13 => 0)
    (fun _ : Fin 13 => []) _ _ base hb
  rw [RepairSource.ProjectionNormalization.StreamPrepare.embed_initial] at he
  let a := TapeEmbedding.receipt (fun _ : Fin 13 => 0) (fun _ : Fin 13 => []) base
  have hat : ∀ j,a.final.tapes (countSlots j)=if j=0 then natWord n++tail else [] := by
    intro j
    change (TapeEmbedding.config (fun _ : Fin 13 => 0) (fun _ : Fin 13 => []) base.final).tapes _=_
    rw [hbf]
    fin_cases j <;> simp [countSlots,Streaming.finished,Streaming.config,TapeEmbedding.config,Fin.addCases]
  have hah : ∀ j,a.final.heads (countSlots j)=0 := by
    intro j
    change (TapeEmbedding.config (fun _ : Fin 13 => 0) (fun _ : Fin 13 => []) base.final).heads _=_
    rw [hbf]
    fin_cases j <;> rfl
  obtain ⟨b,hb,hbs',hsource,hsourceHead,hcount,hcountHead,hother⟩ :=
    Count.focus_run countSlots (by decide) a.final n tail hat hah
  have hab := Composition.run_join copy count _ _ _ a b he hb
  let ab := Composition.joinedReceipt a b
  have fieldTapes' : ∀ j,ab.final.tapes (fieldSlots j)=
      (![[]++natWord n++tail,[],[]] : Fin 3→List Bool) j := by
    intro j
    fin_cases j
    · exact hsource
    · change b.final.tapes 14=[]; rw [(hother 14 (by decide)).1]; rfl
    · change b.final.tapes 15=[]; rw [(hother 15 (by decide)).1]; rfl
  have fieldHeads : ∀ j,ab.final.heads (fieldSlots j)=(![([] : List Bool).length,0,([] : List Bool).length] : Fin 3→ℕ) j := by
    intro j
    fin_cases j
    · exact hsourceHead
    · change b.final.heads 14=0; rw [(hother 14 (by decide)).2]; rfl
    · change b.final.heads 15=0; rw [(hother 15 (by decide)).2]; rfl
  obtain ⟨c,hc,hcs,_,_,hback,hbackHead,hout,houtHead,hcOther⟩ :=
    field_focus fieldSlots (by decide) ab.final n [] tail [] [] fieldTapes' fieldHeads
  have hall := Composition.run_join prefixMachine field _ _ _ ab c hab hc
  have htime : (4*(natWord n++tail).length+2+1+Count.budget n)+1+PCPPQueryField.fieldCost n=budget n tail := by unfold budget; omega
  rw [htime] at hall
  have hi : Composition.leftConfig 4 (Composition.leftConfig _
      (initialConfiguration copy
        (Fin.addCases (fun i : Fin 3 => if i.val=0 then frame (natWord n++tail) else [])
          (fun _ : Fin 13 => []))))=initialConfiguration machine (input n tail) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> rfl
  have hall' : run machine (budget n tail) (input n tail)=some (Composition.joinedReceipt ab c) := by
    change runFrom machine (budget n tail) (initialConfiguration machine (input n tail))=_
    rw [← hi]
    exact hall
  refine ⟨Composition.joinedReceipt ab c,hall',?_,?_,?_,?_,?_,hback,hbackHead,?_,?_⟩
  · change (base.steps+1+b.steps)+1+c.steps ≤ _
    rw [hbs,hcs]
    unfold budget
    omega
  · change c.final.tapes 0=_
    rw [(hcOther 0 (by decide)).1]
    change b.final.tapes 0=_
    rw [(hother 0 (by decide)).1]
    change (TapeEmbedding.config (fun _ : Fin 13 => 0) (fun _ : Fin 13 => []) base.final).tapes 0=_
    rw [hbf]; rfl
  · change c.final.heads 0=0
    rw [(hcOther 0 (by decide)).2]
    change b.final.heads 0=0
    rw [(hother 0 (by decide)).2]
    change (TapeEmbedding.config (fun _ : Fin 13 => 0) (fun _ : Fin 13 => []) base.final).heads 0=0
    rw [hbf]; rfl
  · change c.final.tapes 12=_
    rw [(hcOther 12 (by decide)).1]
    exact hcount
  · change c.final.heads 12=1
    rw [(hcOther 12 (by decide)).2]
    exact hcountHead
  · exact hout
  · exact houtHead

end NearCubicWires.RepairOrdinary.DecompositionSource.Prepare
