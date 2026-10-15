import Proof.CaseAnalysis.CloseoutWitnessFamilyColdRun

/-! Only the ten paid metadata words and existing mass store are live at
the cold family entry. Every private coordinate is genuinely blank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilySparse
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def headers (P H V C T core W L : ℕ) (bits arity : List Bool) : Fin 10→List Bool:=
  ![List.replicate P true,UnaryTemplate.tape core,List.replicate W true,List.replicate L true,
    List.replicate H true,frame arity,List.replicate T true,List.replicate V true,
    List.replicate (natBitLength C) true,frame bits]
def headerSlot (i : Fin 10) : Fin 3243:=![720,2501,2525,2526,2530,3034,3035,3238,3241,3242] i
def massSlot (i : Fin 94) : Fin 3243:=⟨725+i.val,by omega⟩
def data (P H V C T core W L : ℕ) (bits arity : List Bool) (ambient : Fin 94→List Bool) (i : Fin 3243):=
  if h:725 ≤ i.val ∧ i.val<819 then ambient ⟨i.val-725,by omega⟩
  else if i.val=720 then headers P H V C T core W L bits arity 0
  else if i.val=2501 then headers P H V C T core W L bits arity 1
  else if i.val=2525 then headers P H V C T core W L bits arity 2
  else if i.val=2526 then headers P H V C T core W L bits arity 3
  else if i.val=2530 then headers P H V C T core W L bits arity 4
  else if i.val=3034 then headers P H V C T core W L bits arity 5
  else if i.val=3035 then headers P H V C T core W L bits arity 6
  else if i.val=3238 then headers P H V C T core W L bits arity 7
  else if i.val=3241 then headers P H V C T core W L bits arity 8
  else if i.val=3242 then headers P H V C T core W L bits arity 9 else []

theorem store_tape (P H V C T core W L : ℕ) (bits arity : List Bool) (ambient : Fin 94→List Bool)
    (i : Fin 94) : FamilyCold.input P H V C T core W L bits arity ambient (massSlot i)=ambient i:=by
  let j : Fin 3241:=⟨725+i.val,by omega⟩
  have eqslot:massSlot i=j.castAdd 2:=by apply Fin.ext;rfl
  rw [eqslot,FamilyCold.input,FamilyPrepare.tapes,Fin.addCases_left]
  have hp:FamilyBank.parser j=false:=by simp [FamilyBank.parser,j];omega
  have hf:FamilyBank.family j=false:=by simp [FamilyBank.family,j];omega
  have hn:¬(j=721 ∨ j=2531 ∨ j=724):=by
    intro h
    rcases h with h|h|h <;> have hv:=congrArg Fin.val h <;> dsimp [j] at hv <;> omega
  simp only [FamilyInput.blanked,hp,hf,Bool.false_or,Bool.false_eq_true,if_false,if_neg hn]
  have index:j=
      (((((((((i.castAdd 7).natAdd 725).castAdd 1).castAdd 1705).castAdd 1).castAdd 528).castAdd 2).castAdd 1).castAdd 177):=by
    apply Fin.ext;rfl
  rw [index]
  have h724 : (((((i.castAdd 7).natAdd 725).castAdd 1).castAdd 1705).castAdd 1).castAdd 528 ≠ (724 : Fin 3061):=by
    apply Fin.ne_of_val_ne;change 725+i.val≠724;omega
  simp only [FamilyInput.target,FamilyDock.input,FamilyDock.coreData,FamilyLoad.data,Fin.addCases_left,
    Function.update_of_ne h724,SumStorage.data,SumDock.coreData,TermRound.data,TermCommit.data,
    TermMass.data,Fin.addCases_right,TermMass.tail,Fin.addCases_left]

theorem input_eq (P H V C T core W L : ℕ) (bits arity : List Bool) (ambient : Fin 94→List Bool) :
    FamilyCold.input P H V C T core W L bits arity ambient=data P H V C T core W L bits arity ambient:=by
  funext i
  by_cases hm:725 ≤ i.val ∧ i.val<819
  · let j : Fin 94:=⟨i.val-725,by omega⟩
    have he:i=massSlot j:=by apply Fin.ext;dsimp [massSlot,j];omega
    rw [he,store_tape]
    simp only [data,massSlot,dif_pos (show 725 ≤ 725+j.val ∧ 725+j.val<819 by omega),Nat.add_sub_cancel_left]
  by_cases h720:i.val=720
  · have he:i=720:=Fin.ext h720;subst i;rfl
  by_cases h2501:i.val=2501
  · have he:i=2501:=Fin.ext h2501;subst i;rfl
  by_cases h2525:i.val=2525
  · have he:i=2525:=Fin.ext h2525;subst i;rfl
  by_cases h2526:i.val=2526
  · have he:i=2526:=Fin.ext h2526;subst i;rfl
  by_cases h2530:i.val=2530
  · have he:i=2530:=Fin.ext h2530;subst i;rfl
  by_cases h3034:i.val=3034
  · have he:i=3034:=Fin.ext h3034;subst i;rfl
  by_cases h3035:i.val=3035
  · have he:i=3035:=Fin.ext h3035;subst i;rfl
  by_cases h3238:i.val=3238
  · have he:i=3238:=Fin.ext h3238;subst i;rfl
  by_cases h3241:i.val=3241
  · have he:i=3241:=Fin.ext h3241;subst i;rfl
  by_cases h3242:i.val=3242
  · have he:i=3242:=Fin.ext h3242;subst i;rfl
  have hd:data P H V C T core W L bits arity ambient i=[]:=by
    simp only [data,dif_neg hm,if_neg h720,if_neg h2501,if_neg h2525,if_neg h2526,
      if_neg h2530,if_neg h3034,if_neg h3035,if_neg h3238,if_neg h3241,if_neg h3242]
  rw [hd]
  by_cases h826:i.val=826
  · have he:i=826:=Fin.ext h826;subst i;rfl
  by_cases h2515:i.val=2515
  · have he:i=2515:=Fin.ext h2515;subst i;rfl
  by_cases h3059:i.val=3059
  · have he:i=3059:=Fin.ext h3059;subst i;rfl
  let j : Fin 3241:=⟨i.val,by omega⟩
  have he:i=j.castAdd 2:=by apply Fin.ext;rfl
  rw [he,FamilyCold.input,FamilyPrepare.tapes,Fin.addCases_left]
  by_cases hf:(FamilyBank.parser j || FamilyBank.family j)=true
  · simp only [FamilyInput.blanked,hf,if_true]
  · have hr:j=721 ∨ j=2531 ∨ j=724:=by
      have hv:j.val=i.val:=rfl
      simp only [FamilyBank.parser,FamilyBank.family,Bool.or_eq_true,decide_eq_true_eq] at hf
      have h:j.val=721 ∨ j.val=2531 ∨ j.val=724:=by omega
      rcases h with h|h|h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    simp only [FamilyInput.blanked,if_neg hf,if_pos hr]

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilySparse
