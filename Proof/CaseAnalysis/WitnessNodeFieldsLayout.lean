import Proof.CaseAnalysis.WitnessNodeMeaning

/-! One existing tuple extraction supplies all three node fields. The three
fixed decoder workspaces are disjoint and preserve the structural tags. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeFields
open LocalBitMultitape RecoveryRootRound RadixSemantics CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def headerSlots (i : Fin 122) : Fin 668:=i.castAdd 546
def odd (j : Fin 3) : Fin 6:=⟨2*j.val+1,by omega⟩
def sourceSlot (j : Fin 3):=headerSlots (CompetitorWitnessTriple.slots (odd j) 17)
def slots (j : Fin 3) (i : Fin 183) : Fin 668:=
  if i.val=0 then sourceSlot j else ⟨122+182*j.val+(i.val-1),by omega⟩
theorem sourceSlot_val (j : Fin 3) : (sourceSlot j).val=38+40*j.val:=by
  change 20*(2*j.val+1)+17+1=38+40*j.val
  omega
theorem slots_val (j : Fin 3) (i : Fin 183) :
    (slots j i).val=if i.val=0 then 38+40*j.val else 122+182*j.val+(i.val-1):=by
  by_cases hi:i.val=0 <;> simp [slots,hi,sourceSlot_val]
theorem header_injective : Function.Injective headerSlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 668=>a.val) h)
theorem slots_injective (j : Fin 3) : Function.Injective (slots j):=by
  intro a b h
  have hv:=congrArg Fin.val h
  rw [slots_val,slots_val] at hv
  split_ifs at hv
  all_goals apply Fin.ext;omega
theorem slots_disjoint (j k : Fin 3) (hjk : j≠k) (a b : Fin 183) : slots j a≠slots k b:=by
  intro h
  have hv:=congrArg Fin.val h
  have hne:j.val≠k.val:=by intro he;exact hjk (Fin.ext he)
  rw [slots_val,slots_val] at hv
  split_ifs at hv <;> omega

def input (bits : List Bool) : Fin 668→List Bool:=
  Fin.addCases (motive:=fun _ : Fin (122+546)=>List Bool) (CompetitorWitnessTriple.input [] bits) (fun _=>[])
noncomputable def base (bits : List Bool):=
  install headerSlots (input bits) (CompetitorWitnessTriple.stage [] bits 6)
noncomputable def stage (bits : List Bool) (out : Fin 3→Fin 183→List Bool) : ℕ→Fin 668→List Bool
  | 0=>base bits
  | k+1=>if hk:k<3 then install (slots ⟨k,hk⟩) (stage bits out k) (out ⟨k,hk⟩) else stage bits out k

theorem nat_input_eq (bits : List Bool) (i : Fin 183) :
    NatNative.input bits i=if i.val=0 then frame bits else []:=by
  by_cases h0:i.val=0
  · have hi:i=0:=Fin.ext h0
    subst i
    rfl
  · simp [NatNative.input,NatCold.input,CanonicalTest.input,Fin.addCases,h0]

theorem base_input (bits : List Bool) (j : Fin 3) (i : Fin 183) :
    base bits (slots j i)=NatNative.input (NodeMeaning.codeWord bits j) i:=by
  rw [nat_input_eq]
  by_cases hi:i.val=0
  · have hz:i=0:=Fin.ext hi
    subst i
    change install headerSlots (input bits) _ (headerSlots (CompetitorWitnessTriple.slots (odd j) 17))=_
    rw [install_slot _ header_injective]
    exact CompetitorWitnessTriple.field_output [] bits (odd j)
  · rw [if_neg hi]
    have hlarge:122 ≤ (slots j i).val:=by simp only [slots,hi,if_false];omega
    rw [base,install_other _ _ _ _ (by
      intro a ha
      have hv:=congrArg Fin.val ha
      change a.val=(slots j i).val at hv
      omega)]
    simp [input,Fin.addCases,show ¬(slots j i).val<122 by omega]

theorem stage_later (bits : List Bool) (out : Fin 3→Fin 183→List Bool) (j : Fin 3)
    (k : ℕ) (hk : k ≤ j.val) (i : Fin 183) :
    stage bits out k (slots j i)=base bits (slots j i):=by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [stage,dif_pos (by omega : k<3),install_other _ _ _ _ (by
      intro a
      apply slots_disjoint
      intro he
      have hv:=congrArg Fin.val he
      change k=j.val at hv
      omega)]
    exact ih (by omega)

theorem stage_done (bits : List Bool) (out : Fin 3→Fin 183→List Bool) (j : Fin 3)
    (k : ℕ) (hjk : j.val<k) (hk : k ≤ 3) (i : Fin 183) :
    stage bits out k (slots j i)=out j i:=by
  induction k with
  | zero=>omega
  | succ k ih=>
    have hk3:k<3:=by omega
    rw [stage,dif_pos hk3]
    by_cases he:j.val=k
    · have hj:j=⟨k,hk3⟩:=Fin.ext he
      subst j
      exact install_slot _ (slots_injective _) _ _ _
    · rw [install_other _ _ _ _ (by
        intro a
        apply slots_disjoint
        intro h
        have hv:=congrArg Fin.val h
        change k=j.val at hv
        omega)]
      exact ih (by omega) (by omega)

theorem stage_input (bits : List Bool) (out : Fin 3→Fin 183→List Bool) (j : Fin 3) (i : Fin 183) :
    stage bits out j.val (slots j i)=NatNative.input (NodeMeaning.codeWord bits j) i:=by
  rw [stage_later bits out j j.val (by rfl),base_input]

theorem header_retained (bits : List Bool) (out : Fin 3→Fin 183→List Bool)
    (k : ℕ) (hk : k ≤ 3) (i : Fin 122) (hi : ∀ j,sourceSlot j≠headerSlots i) :
    stage bits out k (headerSlots i)=CompetitorWitnessTriple.stage [] bits 6 i:=by
  induction k with
  | zero=>exact install_slot _ header_injective _ _ _
  | succ k ih=>
    rw [stage,dif_pos (by omega : k<3),install_other _ _ _ _ (by
      intro a he
      by_cases ha:a.val=0
      · exact hi ⟨k,by omega⟩ (by simpa only [slots,ha,if_true] using he)
      · have hv:=congrArg Fin.val he
        simp only [slots,ha,if_false,headerSlots,Fin.val_castAdd] at hv
        omega)]
    exact ih (by omega)

theorem codeWord_length (bits : List Bool) (i : Fin 3) : (NodeMeaning.codeWord bits i).length=bits.length:=
  (RecoveryFixedUnpair.word_lengths _).1.trans (CompetitorWitnessTriple.word_length bits _)

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeFields
