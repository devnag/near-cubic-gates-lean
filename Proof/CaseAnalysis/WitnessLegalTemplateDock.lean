import Proof.CaseAnalysis.WitnessLegalTemplate

/-! Four retained actual source-policy fields enter the legal-policy worker
by tape aliasing, with the source domain kept at its documented head one. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.LegalTemplate.Call
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev extra (e : ℕ):=LegalTemplate.tapes e
def values (R q0 cb b : ℕ) : Fin 4→List Bool:=
  ![UnaryTemplate.tape R,List.replicate q0 true,List.replicate cb true,List.replicate b true]
def cursors (i : Fin 4) : ℕ:=if i.val=0 then 1 else 0
def initialData (e R q0 cb b i : ℕ):=
  if i=0 then values R q0 cb b 0 else if i=5+LegalPolicy.M e then values R q0 cb b 1
  else if i=5+LegalPolicy.M e+16 then values R q0 cb b 2
  else if i=5+LegalPolicy.M e+138 then values R q0 cb b 3 else []

theorem input_fields (e R q0 cb b : ℕ) (i : Fin (extra e)) :
    LegalTemplate.input e R q0 cb b i=initialData e R q0 cb b i.val:=by
  have hm:0<LegalPolicy.M e:=by dsimp [LegalPolicy.M,ModeWire.tapes,ModeDivide.tapes];omega
  refine Fin.addCases (m:=5) (n:=L e) (fun j=>?_) (fun j=>?_) i
  · have raw:MatrixTemplateCopy.resetInput R j=(if j.val=0 then UnaryTemplate.tape R else []):=by
      fin_cases j <;> rfl
    rw [LegalTemplate.input,Fin.addCases_left,raw]
    simp only [initialData,Fin.val_castAdd,
      if_neg (show j.val≠5+LegalPolicy.M e by omega),
      if_neg (show j.val≠5+LegalPolicy.M e+16 by omega),
      if_neg (show j.val≠5+LegalPolicy.M e+138 by omega)]
    rfl
  · rw [LegalTemplate.input,Fin.addCases_right]
    simp only [initialData,Fin.val_natAdd,if_neg (show 5+j.val≠0 by omega),Nat.add_left_cancel_iff]
    by_cases hj:j.val=0
    · simp only [LegalPolicy.input,hj,ite_true,List.replicate_zero]
      rw [if_neg (show 0≠LegalPolicy.M e by omega),
        if_neg (show 5+0≠5+LegalPolicy.M e+16 by omega),
        if_neg (show 5+0≠5+LegalPolicy.M e+138 by omega)]
    · simp only [LegalPolicy.input,if_neg hj,values]
      have h16:(5+j.val=5+LegalPolicy.M e+16) ↔ j.val=LegalPolicy.M e+16:=by omega
      have h138:(5+j.val=5+LegalPolicy.M e+138) ↔ j.val=LegalPolicy.M e+138:=by omega
      simp only [h16,h138]
      rfl

def old (e : ℕ) {t : ℕ} (i : Fin t) : Fin (t+extra e):=i.castAdd _
def remap (e : ℕ) (i : Fin (extra e)) : Fin (4+extra e):=
  if i.val=0 then (0 : Fin 4).castAdd _
  else if i.val=5+LegalPolicy.M e then (1 : Fin 4).castAdd _
  else if i.val=5+LegalPolicy.M e+16 then (2 : Fin 4).castAdd _
  else if i.val=5+LegalPolicy.M e+138 then (3 : Fin 4).castAdd _ else i.natAdd 4
def bank (e : ℕ) {t : ℕ} (fields : Fin 4→Fin t) : Fin (4+extra e)→Fin (t+extra e):=
  Fin.addCases (motive:=fun _=>Fin (t+extra e)) (fun i=>old e (fields i)) (fun i=>i.natAdd t)
def slots (e : ℕ) {t : ℕ} (fields : Fin 4→Fin t):=bank e fields ∘ remap e
def input (e : ℕ) {t : ℕ} (data : Fin t→List Bool) : Fin (t+extra e)→List Bool:=
  Fin.addCases data (fun _=>[])
def heads (e : ℕ) {t : ℕ} (cursor : Fin t→ℕ) : Fin (t+extra e)→ℕ:=
  Fin.addCases cursor (fun _=>0)
def machine (e den : ℕ) (delta : ℚ) (copies : ℕ) (sym : Bool) {t : ℕ} (fields : Fin 4→Fin t):=
  RecoveryFocus.machine (slots e fields) (LegalTemplate.machine e den delta copies sym)

theorem remap_injective (e : ℕ) : Function.Injective (remap e):=by
  intro i j he
  have hv:=congrArg Fin.val he
  dsimp only [remap] at hv
  split_ifs at hv <;> dsimp at hv <;> apply Fin.ext <;> omega
theorem slots_injective (e : ℕ) {t : ℕ} (fields : Fin 4→Fin t) (hf : Function.Injective fields) :
    Function.Injective (slots e fields):=by
  apply Function.Injective.comp (g:=bank e fields) _ (remap_injective e)
  apply RecoveryColdAllCode.join_injective
  · intro i j he
    have hv:=congrArg Fin.val he
    exact hf (Fin.ext hv)
  · intro i j he
    have hv:=congrArg Fin.val he
    simp only [Fin.val_natAdd] at hv
    exact Fin.ext (by omega)
  · intro i j he
    have hv:=congrArg Fin.val he
    have ht:=(fields i).isLt
    dsimp only [old,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega

theorem input_local (e : ℕ) {t : ℕ} (fields : Fin 4→Fin t) (data : Fin t→List Bool) (R q0 cb b : ℕ)
    (hf : ∀ i,data (fields i)=values R q0 cb b i) (i : Fin (extra e)) :
    input e data (slots e fields i)=LegalTemplate.input e R q0 cb b i:=by
  rw [input_fields]
  by_cases h0:i.val=0
  · simpa [input,slots,bank,remap,old,initialData,h0] using hf 0
  by_cases h1:i.val=5+LegalPolicy.M e
  · simpa [input,slots,bank,remap,old,initialData,h0,h1] using hf 1
  by_cases h2:i.val=5+LegalPolicy.M e+16
  · simpa [input,slots,bank,remap,old,initialData,h0,h1,h2] using hf 2
  by_cases h3:i.val=5+LegalPolicy.M e+138
  · simpa [input,slots,bank,remap,old,initialData,h0,h1,h2,h3] using hf 3
  simp [input,slots,bank,remap,initialData,h0,h1,h2,h3]

theorem heads_local (e : ℕ) {t : ℕ} (fields : Fin 4→Fin t) (cursor : Fin t→ℕ)
    (hf : ∀ i,cursor (fields i)=cursors i) (i : Fin (extra e)) :
    heads e cursor (slots e fields i)=LegalTemplate.heads e i:=by
  by_cases h0:i.val=0
  · simpa [heads,slots,bank,remap,old,LegalTemplate.heads,h0,cursors] using hf 0
  by_cases h1:i.val=5+LegalPolicy.M e
  · simpa [heads,slots,bank,remap,old,LegalTemplate.heads,h0,h1,cursors] using hf 1
  by_cases h2:i.val=5+LegalPolicy.M e+16
  · simpa [heads,slots,bank,remap,old,LegalTemplate.heads,h0,h1,h2,cursors] using hf 2
  by_cases h3:i.val=5+LegalPolicy.M e+138
  · simpa [heads,slots,bank,remap,old,LegalTemplate.heads,h0,h1,h2,h3,cursors] using hf 3
  simp [heads,slots,bank,remap,LegalTemplate.heads,h0,h1,h2,h3]

theorem outside (e : ℕ) {t : ℕ} (fields : Fin 4→Fin t) (i : Fin t) (hi : ∀ j,fields j≠i) :
    ∀ j,slots e fields j≠old e i:=by
  have away:∀ z,bank e fields z≠old e i:=by
    intro z
    refine Fin.addCases (m:=4) (n:=extra e) (fun j=>?_) (fun j=>?_) z
    · intro he
      have hv:=congrArg Fin.val he
      simp only [bank,Fin.addCases_left,old,Fin.val_castAdd] at hv
      exact hi j (Fin.ext hv)
    · intro he
      have hv:=congrArg Fin.val he
      simp only [bank,Fin.addCases_right,old,Fin.val_castAdd,Fin.val_natAdd] at hv
      have ht:=i.isLt
      omega
  exact fun j=>away (remap e j)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.LegalTemplate.Call
