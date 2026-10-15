import Proof.CaseAnalysis.WitnessNodeScalar
import Proof.CaseAnalysis.WitnessNodeDecision

/-! The node guard shares its fixed small driver, binary width, arity and
current-index tapes across three identical scalar calls. Every other call
workspace is disjoint. The five tuple markers reuse the existing classifier. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeGuard
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fieldSlots (i : Fin 668) : Fin 746:=i.castAdd 78
def common (i : Fin 4) : Fin 746:=⟨668+i.val,by omega⟩
def scalarSlots (j : Fin 3) (i : Fin 21) : Fin 746:=
  if hi:i.val<4 then common ⟨i.val,hi⟩
  else if i.val=4 then fieldSlots (NodeFields.slots j 174)
  else ⟨672+16*j.val+(i.val-5),by omega⟩
def kindSource : Fin 5 → Fin 122:=![18,58,98,79,119]
def kindValues (bits : List Bool) : Fin 5 → List Bool:=
  ![RecoveryFixedUnpair.leftWord (CompetitorWitnessTriple.word bits 0),
    RecoveryFixedUnpair.leftWord (CompetitorWitnessTriple.word bits 2),
    RecoveryFixedUnpair.leftWord (CompetitorWitnessTriple.word bits 4),
    CompetitorWitnessTriple.word bits 4,CompetitorWitnessTriple.word bits 6]
def kindSlots (j : Fin 5) (i : Fin 6) : Fin 746:=
  if i.val=0 then fieldSlots (NodeFields.headerSlots (kindSource j))
  else ⟨720+5*j.val+(i.val-1),by omega⟩

theorem field_injective : Function.Injective fieldSlots:=by
  intro a b h;exact Fin.ext (congrArg (fun i : Fin 746=>i.val) h)
theorem scalar_val (j : Fin 3) (i : Fin 21) : (scalarSlots j i).val=
    if i.val<4 then 668+i.val else if i.val=4 then 295+182*j.val else 672+16*j.val+(i.val-5):=by
  by_cases hi:i.val<4
  · simp [scalarSlots,hi,common]
  · by_cases h4:i.val=4
    · simp [scalarSlots,h4,fieldSlots,NodeFields.slots]
      omega
    · simp [scalarSlots,hi,h4]
theorem scalar_injective (j : Fin 3) : Function.Injective (scalarSlots j):=by
  intro a b h
  have hv:=congrArg Fin.val h
  rw [scalar_val,scalar_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem scalar_common (j : Fin 3) (i : Fin 4) : scalarSlots j (i.castAdd 17)=common i:=by
  apply Fin.ext
  simp [scalar_val,i.isLt,common]
theorem scalar_disjoint (j k : Fin 3) (hne : j≠k) (i z : Fin 21) (hi : 4 ≤ i.val) :
    scalarSlots k z≠scalarSlots j i:=by
  intro h
  have hv:=congrArg Fin.val h
  have hn:j.val≠k.val:=by intro he;exact hne (Fin.ext he)
  rw [scalar_val,scalar_val] at hv
  split_ifs at hv <;> omega
theorem kind_injective (j : Fin 5) : Function.Injective (kindSlots j):=by
  fin_cases j <;> decide
theorem kind_disjoint (j k : Fin 5) (h : j≠k) (i z : Fin 6) : kindSlots k z≠kindSlots j i:=by
  fin_cases j <;> fin_cases k <;> first | exact False.elim (h rfl) | (revert i z;decide)
theorem kind_val (j : Fin 5) (i : Fin 6) : (kindSlots j i).val=
    if i.val=0 then (kindSource j).val else 720+5*j.val+(i.val-1):=by
  by_cases hi:i.val=0 <;> simp [kindSlots,hi,fieldSlots,NodeFields.headerSlots]
theorem scalar_kind_disjoint (j : Fin 3) (k : Fin 5) (i : Fin 21) (z : Fin 6) :
    scalarSlots j i≠kindSlots k z:=by
  intro h
  have hv:=congrArg Fin.val h
  rw [scalar_val,kind_val] at hv
  have hk:(kindSource k).val<122:=(kindSource k).isLt
  split_ifs at hv <;> omega

def shared (w : ℕ) (left right : List Bool) : Fin 4 → List Bool:=
  ![List.replicate 3 true,List.replicate w true,frame left,frame right]
theorem input_shared (w : ℕ) (left right bits : List Bool) (i : Fin 4) :
    NodeScalar.input w left right bits (i.castAdd 17)=shared w left right i:=by
  fin_cases i <;> rfl
def base (fields : Fin 668 → List Bool) (w : ℕ) (left right : List Bool) : Fin 746 → List Bool:=
  Fin.addCases (motive:=fun _ : Fin (668+78) => List Bool) fields
    (Fin.addCases (motive:=fun _ : Fin (4+74) => List Bool) (shared w left right) (fun _=>[]))
theorem base_field (fields : Fin 668 → List Bool) (w : ℕ) (left right : List Bool) (i : Fin 668) :
    base fields w left right (fieldSlots i)=fields i:=by
  simp only [base,fieldSlots,Fin.addCases_left]
theorem base_common (fields : Fin 668 → List Bool) (w : ℕ) (left right : List Bool) (i : Fin 4) :
    base fields w left right (common i)=shared w left right i:=by
  change base fields w left right ((i.castAdd 74).natAdd 668)=_
  simp only [base,Fin.addCases_right,Fin.addCases_left]
theorem base_blank (fields : Fin 668 → List Bool) (w : ℕ) (left right : List Bool) (i : Fin 746)
    (hi : 672 ≤ i.val) : base fields w left right i=[]:=by
  simp [base,Fin.addCases,show ¬i.val<668 by omega,show ¬i.val-668<4 by omega]

noncomputable def scalarStage (start : Fin 746 → List Bool) (out : Fin 3 → Fin 21 → List Bool) :
    ℕ → Fin 746 → List Bool
  | 0=>start
  | k+1=>if hk:k<3 then install (scalarSlots ⟨k,hk⟩) (scalarStage start out k) (out ⟨k,hk⟩)
      else scalarStage start out k

theorem scalar_stage_common (start : Fin 746 → List Bool) (out : Fin 3 → Fin 21 → List Bool)
    (data : Fin 4 → List Bool) (hi : ∀ i,start (common i)=data i)
    (ho : ∀ j i,out j (i.castAdd 17)=data i) (k : ℕ) (i : Fin 4) :
    scalarStage start out k (common i)=data i:=by
  induction k with
  | zero=>exact hi i
  | succ k ih=>
    rw [scalarStage]
    split_ifs with hk
    · rw [←scalar_common ⟨k,hk⟩ i,install_slot _ (scalar_injective _)]
      exact ho _ i
    · exact ih

theorem scalar_stage_later (start : Fin 746 → List Bool) (out : Fin 3 → Fin 21 → List Bool)
    (j : Fin 3) (k : ℕ) (hk : k ≤ j.val) (i : Fin 21) (hi : 4 ≤ i.val) :
    scalarStage start out k (scalarSlots j i)=start (scalarSlots j i):=by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [scalarStage,dif_pos (by omega : k<3),install_other _ _ _ _ (by
      intro z
      apply scalar_disjoint j ⟨k,by omega⟩ _ i z hi
      intro h
      have hv:=congrArg Fin.val h
      change j.val=k at hv
      omega)]
    exact ih (by omega)

theorem scalar_stage_done (start : Fin 746 → List Bool) (out : Fin 3 → Fin 21 → List Bool)
    (j : Fin 3) (k : ℕ) (hk : j.val<k) (hk3 : k ≤ 3) (i : Fin 21) (hi : 4 ≤ i.val) :
    scalarStage start out k (scalarSlots j i)=out j i:=by
  induction k with
  | zero=>omega
  | succ k ih=>
    rw [scalarStage,dif_pos (by omega : k<3)]
    by_cases he:k=j.val
    · have hj:(⟨k,by omega⟩ : Fin 3)=j:=Fin.ext he
      rw [hj,install_slot _ (scalar_injective j)]
    · rw [install_other _ _ _ _ (by
        intro z
        apply scalar_disjoint j ⟨k,by omega⟩ _ i z hi
        intro h
        exact he (congrArg Fin.val h.symm))]
      exact ih (by omega) (by omega)

theorem scalar_stage_other (start : Fin 746 → List Bool) (out : Fin 3 → Fin 21 → List Bool)
    (k : ℕ) (i : Fin 746) (hi : ∀ j z,scalarSlots j z≠i) : scalarStage start out k i=start i:=by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [scalarStage]
    split_ifs with hk
    · rw [install_other _ _ _ _ (hi _)];exact ih
    · exact ih

theorem scalar_base_input (fields : Fin 668 → List Bool) (w : ℕ) (left right : List Bool)
    (payload : Fin 3 → List Bool) (hp : ∀ j,fields (NodeFields.slots j 174)=frame (payload j))
    (j : Fin 3) (i : Fin 21) :
    base fields w left right (scalarSlots j i)=NodeScalar.input w left right (payload j) i:=by
  by_cases hi:i.val<4
  · let k : Fin 4:=⟨i.val,hi⟩
    have he:i=k.castAdd 17:=Fin.ext rfl
    rw [he,scalar_common,base_common]
    exact (input_shared w left right (payload j) k).symm
  · by_cases h4:i.val=4
    · have he:i=4:=Fin.ext h4
      subst i
      change base fields w left right (fieldSlots (NodeFields.slots j 174))=_
      rw [base_field,hp];rfl
    · rw [base_blank _ _ _ _ _ (by rw [scalar_val,if_neg hi,if_neg h4];omega)]
      fin_cases i <;> simp_all [NodeScalar.input]

def kindResult (bits : List Bool) (j : Fin 5):=CompetitorWitnessKind.tapes
  (CompetitorWitnessKind.after (kindValues bits j)) (CompetitorWitnessKind.flags (kindValues bits j))
  (2*(kindValues bits j).length+1)
noncomputable def kindStage (start : Fin 746 → List Bool) (bits : List Bool) : ℕ → Fin 746 → List Bool
  | 0=>start
  | k+1=>if hk:k<5 then install (kindSlots ⟨k,hk⟩) (kindStage start bits k) (kindResult bits ⟨k,hk⟩)
      else kindStage start bits k

theorem kind_lengths (bits : List Bool) (j : Fin 5) : (kindValues bits j).length=bits.length:=by
  fin_cases j <;> simp [kindValues,RecoveryFixedUnpair.word_lengths,CompetitorWitnessTriple.word_length]

theorem kind_stage_later (start : Fin 746 → List Bool) (bits : List Bool)
    (j : Fin 5) (k : ℕ) (hk : k ≤ j.val) (i : Fin 6) :
    kindStage start bits k (kindSlots j i)=start (kindSlots j i):=by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [kindStage,dif_pos (by omega : k<5),install_other _ _ _ _ (by
      intro z
      apply kind_disjoint j ⟨k,by omega⟩ _ i z
      intro h
      have hv:=congrArg Fin.val h
      change j.val=k at hv
      omega)]
    exact ih (by omega)

theorem kind_stage_done (start : Fin 746 → List Bool) (bits : List Bool)
    (j : Fin 5) (k : ℕ) (hk : j.val<k) (hk5 : k ≤ 5) (i : Fin 6) :
    kindStage start bits k (kindSlots j i)=kindResult bits j i:=by
  induction k with
  | zero=>omega
  | succ k ih=>
    rw [kindStage,dif_pos (by omega : k<5)]
    by_cases he:k=j.val
    · have hj:(⟨k,by omega⟩ : Fin 5)=j:=Fin.ext he
      rw [hj,install_slot _ (kind_injective j)]
    · rw [install_other _ _ _ _ (by
        intro z
        apply kind_disjoint j ⟨k,by omega⟩ _ i z
        intro h
        exact he (congrArg Fin.val h.symm))]
      exact ih (by omega) (by omega)

theorem kind_stage_other (start : Fin 746 → List Bool) (bits : List Bool)
    (k : ℕ) (i : Fin 746) (hi : ∀ j z,kindSlots j z≠i) : kindStage start bits k i=start i:=by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [kindStage]
    split_ifs with hk
    · rw [install_other _ _ _ _ (hi _)];exact ih
    · exact ih

theorem kind_initial_input (fields : Fin 668 → List Bool) (w : ℕ) (left right bits : List Bool)
    (out : Fin 3 → Fin 21 → List Bool)
    (hs : ∀ j,fields (NodeFields.headerSlots (kindSource j))=frame (kindValues bits j))
    (j : Fin 5) (i : Fin 6) :
    scalarStage (base fields w left right) out 3 (kindSlots j i)=CompetitorWitnessKind.input (kindValues bits j) i:=by
  rw [scalar_stage_other _ _ _ _ (by intro k z;exact scalar_kind_disjoint k j z i)]
  by_cases hi:i.val=0
  · have he:i=0:=Fin.ext hi
    subst i
    change base fields w left right (fieldSlots (NodeFields.headerSlots (kindSource j)))=_
    rw [base_field,hs];rfl
  · rw [base_blank _ _ _ _ _ (by simp only [kindSlots,hi,if_false];omega)]
    exact (by simp [CompetitorWitnessKind.input,hi])

theorem fields_kind_values (bits : List Bool) (fields : Fin 668 → List Bool)
    (hf : ∀ i : Fin 122,(∀ j,NodeFields.sourceSlot j≠NodeFields.headerSlots i) →
      fields (NodeFields.headerSlots i)=CompetitorWitnessTriple.stage [] bits 6 i)
    (j : Fin 5) : fields (NodeFields.headerSlots (kindSource j))=frame (kindValues bits j):=by
  rw [hf _ (by fin_cases j <;> decide)]
  fin_cases j
  · exact CompetitorWitnessTriple.field_output [] bits 0
  · exact CompetitorWitnessTriple.field_output [] bits 2
  · exact CompetitorWitnessTriple.field_output [] bits 4
  · exact PCPPNativeCanonical.tail_retained [] bits
  · exact CompetitorWitnessTriple.tail_output [] bits

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeGuard
