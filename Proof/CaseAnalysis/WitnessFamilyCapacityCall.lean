import Proof.CaseAnalysis.WitnessFamilyCapacity

/-! The already-retained N counter pays both family capacities without
rescanning the original input or disturbing the live source/policy bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCapacity.Call
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev extra (E : ℕ):=FamilyCapacity.tapes E
def old (E : ℕ) {t : ℕ} (i : Fin t) : Fin (t+extra E):=i.castAdd _
def slots (E : ℕ) {t : ℕ} (source : Fin t) (i : Fin (extra E)) : Fin (t+extra E):=
  if i.val=0 then old E source else i.natAdd t
def input (E : ℕ) {t : ℕ} (data : Fin t→List Bool) : Fin (t+extra E)→List Bool:=
  Fin.addCases (m:=t) (n:=extra E) (motive:=fun _=>List Bool) data (fun _=>[])
def heads (E : ℕ) {t : ℕ} (cursor : Fin t→ℕ) : Fin (t+extra E)→ℕ:=
  Fin.addCases (m:=t) (n:=extra E) (motive:=fun _=>ℕ) cursor (fun _=>0)
def machine (E K : ℕ) {t : ℕ} (source : Fin t):=
  RecoveryFocus.machine (slots E source) (FamilyCapacity.machine E K)

theorem slots_injective (E : ℕ) {t : ℕ} (source : Fin t) : Function.Injective (slots E source):=by
  intro i j he
  have hv:=congrArg Fin.val he
  dsimp only [slots] at hv
  split_ifs at hv <;> dsimp only [old,Fin.val_castAdd,Fin.val_natAdd] at hv
  all_goals apply Fin.ext;have hs:=source.isLt;omega

theorem outside (E : ℕ) {t : ℕ} (source i : Fin t) (hi : source≠i) :
    ∀ j,slots E source j≠old E i:=by
  intro j he
  have hv:=congrArg Fin.val he
  dsimp only [slots] at hv
  split_ifs at hv
  · exact hi (Fin.ext hv)
  · have ht:=i.isLt
    dsimp only [old,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega

theorem call_run (E K N : ℕ) (hK : 0<K) {t : ℕ} (source : Fin t)
    (data : Fin t→List Bool) (cursor : Fin t→ℕ)
    (hd : data source=List.replicate N true) (hh : cursor source=0) :
    ∃ actual,runFrom (machine E K source) (FamilyCapacity.budget E K N)
      ⟨(machine E K source).start,heads E cursor,input E data⟩=some actual ∧
      actual.steps≤FamilyCapacity.budget E K N ∧
      (∀ i,actual.final.heads (slots E source i)=0) ∧
      actual.final.tapes (slots E source (FamilyCapacity.pSlot E))=
        List.replicate (FamilyCapacity.value E K N) true ∧
      actual.final.tapes (slots E source (FamilyCapacity.hSlot E))=
        List.replicate (FamilyCapacity.value E K N+1) true ∧
      (∀ i,actual.final.heads (old E i)=cursor i ∧ actual.final.tapes (old E i)=data i):=by
  obtain ⟨output,inner,hN,hP,hH⟩:=FamilyCapacity.capacity_run E K N hK
  obtain ⟨r,run,rt,rh,rs⟩:=inner
  have inputFields (i : Fin (extra E)):input E data (slots E source i)=FamilyCapacity.input E N i:=by
    by_cases h0:i.val=0
    · simp only [slots,if_pos h0,input,old,Fin.addCases_left,FamilyCapacity.input]
      exact hd
    · simp only [slots,input,Fin.addCases_right,FamilyCapacity.input,if_neg h0]
  have headFields (i : Fin (extra E)):heads E cursor (slots E source i)=0:=by
    by_cases h0:i.val=0
    · simp only [slots,if_pos h0,heads,old,Fin.addCases_left];exact hh
    · simp only [slots,if_neg h0,heads,Fin.addCases_right]
  have dock:=RecoveryFocus.dock (slots E source) (slots_injective E source)
    (FamilyCapacity.machine E K) _ (heads E cursor) (input E data)
    (initialConfiguration (FamilyCapacity.machine E K) (FamilyCapacity.input E N))
    headFields inputFields r run
  let actual:=Classical.choose dock
  have facts:=Classical.choose_spec dock
  have ah:=facts.2.2.2.1
  have atapes:=facts.2.2.2.2.1
  have away:=facts.2.2.2.2.2
  refine ⟨actual,facts.1,facts.2.2.1.trans_le rs,fun i=>(ah i).trans (rh i),
    (atapes _).trans ((congrFun rt _).trans hP),(atapes _).trans ((congrFun rt _).trans hH),?_⟩
  intro i
  by_cases hi:source=i
  · subst i
    let z : Fin (extra E):=⟨0,by dsimp [extra,FamilyCapacity.tapes,FamilyCapacity.A,RepairSource.ProjectionNormalization.DimensionPolynomial.tapes];omega⟩
    have he:slots E source z=old E source:=by simp only [slots,z,if_true]
    exact ⟨he ▸ ((ah z).trans (rh z)).trans hh.symm,
      he ▸ ((atapes z).trans ((congrFun rt _).trans hN)).trans hd.symm⟩
  · have keep:=away (old E i) (outside E source i hi)
    exact ⟨keep.1.trans (by simp only [heads,old,Fin.addCases_left]),
      keep.2.trans (by simp only [input,old,Fin.addCases_left])⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCapacity.Call
