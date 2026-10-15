import Proof.Circuits.DecompositionAtom

/-! Cold ordinary input framing and the two actual native header counts.
The retained raw source stops at the first signed child field. -/
namespace NearCubicWires.RepairOrdinary.DecompositionInputCounts
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def aritySlots : Fin 11 → Fin 23 := ![1,3,4,5,6,7,8,9,10,11,12]
def countSlots : Fin 11 → Fin 23 := ![1,13,14,15,16,17,18,19,20,21,22]
def copy := TapeEmbedding.machine 20 Streaming.machine
noncomputable def arityProgram := RecoveryFocus.machine aritySlots PCPPQueryNatural.machine
noncomputable def countProgram := RecoveryFocus.machine countSlots PCPPQueryNatural.machine
noncomputable def prefixMachine := Composition.machine copy arityProgram
noncomputable def machine := Composition.machine prefixMachine countProgram
def word (arity count : ℕ) (tail : List Bool) := natWord arity++natWord count++tail
def input (arity count : ℕ) (tail : List Bool) (i : Fin 23) : List Bool :=
  if i.val=0 then frame (word arity count tail) else []
def budget (arity count : ℕ) (tail : List Bool) :=
  4*(word arity count tail).length+PCPPQueryNatural.budget arity+PCPPQueryNatural.budget count+4

def prefixBudget (arity count : ℕ) (tail : List Bool) :=
  4*(word arity count tail).length+PCPPQueryNatural.budget arity+3

theorem arity_fresh (i : Fin 23) (hi : 13 ≤ i.val) : RecoveryFocus.pick aritySlots i=none := by
  have hn : ¬∃ j,aritySlots j=i := by
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    fin_cases j <;> norm_num [aritySlots] at hv <;> omega
  simp only [RecoveryFocus.pick,dif_neg hn]

theorem prefix_run (arity count : ℕ) (tail : List Bool) :
    ∃ r,run prefixMachine (prefixBudget arity count tail) (input arity count tail)=some r ∧
      r.final.tapes 0=frame (word arity count tail) ∧ r.final.heads 0=0 ∧
      r.final.tapes 1=word arity count tail ∧ r.final.heads 1=(natWord arity).length ∧
      r.final.tapes 12=UnaryTemplate.tape arity ∧ r.final.heads 12=1 ∧
      (∀ i : Fin 23,13 ≤ i.val → r.final.tapes i=[] ∧ r.final.heads i=0) ∧
      r.steps ≤ prefixBudget arity count tail := by
  obtain ⟨base,hb,bf,bs,_⟩ := Streaming.copy_run (word arity count tail)
  let copied := TapeEmbedding.receipt (fun _ : Fin 20 => 0) (fun _ => []) base
  have hc := TapeEmbedding.run_embed Streaming.machine (fun _ : Fin 20 => 0)
    (fun _ => []) _ _ base hb
  rw [RepairSource.ProjectionNormalization.StreamPrepare.embed_initial] at hc
  have input_eq : (Fin.addCases (m:=3) (n:=20) (motive:=fun _ => List Bool)
      (fun i : Fin 3 => if i.val=0 then frame (word arity count tail) else [])
      (fun _ : Fin 20 => []))=input arity count tail := by
    funext i
    refine Fin.addCases (m:=3) (n:=20) (fun j => ?_) (fun j => ?_) i
    · fin_cases j <;> rfl
    · simp [input]
  rw [input_eq] at hc
  have arityTapes (j : Fin 11) : copied.final.tapes (aritySlots j)=
      if j=0 then []++natWord arity++(natWord count++tail) else [] := by
    simp only [copied,TapeEmbedding.receipt,bf,TapeEmbedding.config]
    fin_cases j <;> simp [aritySlots,Streaming.finished,Streaming.config,Fin.addCases,word,List.append_assoc]
  have ah (j : Fin 11) : copied.final.heads (aritySlots j)=if j=0 then ([] : List Bool).length else 0 := by
    simp only [copied,TapeEmbedding.receipt,bf,TapeEmbedding.config]
    fin_cases j <;> rfl
  obtain ⟨a,ha,aritySteps,at1,ah1,at12,ah12,aOther⟩ :=
    PCPPQueryNatural.focus_run aritySlots (by decide) copied.final [] (natWord count++tail) arity arityTapes ah
  have hprefix := Composition.run_join copy arityProgram _ _ _ copied a hc ha
  have he : (4*(word arity count tail).length+2)+1+PCPPQueryNatural.budget arity=
      prefixBudget arity count tail := by unfold prefixBudget; omega
  rw [he] at hprefix
  refine ⟨Composition.joinedReceipt copied a,hprefix,?_,?_,?_,?_,at12,ah12,?_,?_⟩
  · change a.final.tapes 0=_
    rw [(aOther 0 (by decide)).1]
    simp only [copied,TapeEmbedding.receipt,bf,TapeEmbedding.config]
    rfl
  · change a.final.heads 0=0
    rw [(aOther 0 (by decide)).2]
    simp only [copied,TapeEmbedding.receipt,bf,TapeEmbedding.config]
    rfl
  · change a.final.tapes (aritySlots 0)=word arity count tail
    simpa only [word,List.nil_append,List.append_assoc] using at1
  · change a.final.heads (aritySlots 0)=(natWord arity).length
    simpa only [List.length_nil,Nat.zero_add,DecompositionSource.natWord_length] using ah1
  · intro i hi
    change a.final.tapes i=[] ∧ a.final.heads i=0
    rw [(aOther i (arity_fresh i hi)).1,(aOther i (arity_fresh i hi)).2]
    simp [copied,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,show ¬i.val<3 by omega]
  · change base.steps+1+a.steps ≤ _
    unfold prefixBudget
    omega

end NearCubicWires.RepairOrdinary.DecompositionInputCounts
