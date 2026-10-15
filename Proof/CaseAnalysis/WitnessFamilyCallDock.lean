import Proof.CaseAnalysis.WitnessFamilySparsePorts

/-! The paid policy and mass store enter the whole family by direct tape
aliasing. All private tapes are fresh; no metadata serialization is run. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCold.Call
open LocalBitMultitape FamilySparse
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev extra:=3243
def remap (i : Fin 3243) : Fin (104+3243):=
  if h:∃ j,port j=i then (Classical.choose h).castAdd 3243 else i.natAdd 104
def unmap : Fin (104+3243)→Fin 3243:=
  Fin.addCases (m:=104) (n:=3243) (motive:=fun _=>Fin 3243) port id

theorem unmap_remap (i : Fin 3243) : unmap (remap i)=i:=by
  unfold remap
  split_ifs with h
  · simp only [unmap,Fin.addCases_left]
    exact Classical.choose_spec h
  · simp only [unmap,Fin.addCases_right,id_eq]
theorem remap_injective : Function.Injective remap:=Function.LeftInverse.injective unmap_remap

theorem remap_port (j : Fin 104) : remap (port j)=j.castAdd 3243:=by
  have h:∃ k,port k=port j:=⟨j,rfl⟩
  rw [remap,dif_pos h]
  exact congrArg (Fin.castAdd 3243) (port_injective (Classical.choose_spec h))
theorem remap_other (i : Fin 3243) (hi : ∀ j,port j≠i) : remap i=i.natAdd 104:=by
  rw [remap,dif_neg (by simpa using hi)]

def old {t : ℕ} (i : Fin t) : Fin (t+extra):=i.castAdd extra
def bank {t : ℕ} (fields : Fin 104→Fin t) : Fin (104+3243)→Fin (t+extra):=
  Fin.addCases (m:=104) (n:=3243) (motive:=fun _=>Fin (t+extra))
    (fun i=>old (fields i)) (fun i=>i.natAdd t)
def slots {t : ℕ} (fields : Fin 104→Fin t):=bank fields ∘ remap

theorem slots_injective {t : ℕ} (fields : Fin 104→Fin t) (hf : Function.Injective fields) :
    Function.Injective (slots fields):=by
  apply Function.Injective.comp (g:=bank fields) _ remap_injective
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

def input {t : ℕ} (data : Fin t→List Bool) : Fin (t+extra)→List Bool:=
  Fin.addCases (m:=t) (n:=extra) (motive:=fun _=>List Bool) data (fun _=>[])
def heads {t : ℕ} (cursor : Fin t→ℕ) : Fin (t+extra)→ℕ:=
  Fin.addCases (m:=t) (n:=extra) (motive:=fun _=>ℕ) cursor (fun _=>0)
def machine (sym : Bool) (k : ℕ) (q : ℚ) {t : ℕ} (fields : Fin 104→Fin t):=
  RecoveryFocus.machine (slots fields) (FamilyCold.machine sym k q)

theorem input_local {t : ℕ} (fields : Fin 104→Fin t) (data : Fin t→List Bool)
    (P H V C T core W L : ℕ) (bits arity : List Bool) (ambient : Fin 94→List Bool)
    (hf : ∀ j,data (fields j)=values P H V C T core W L bits arity ambient j) (i : Fin 3243) :
    input data (slots fields i)=FamilyCold.input P H V C T core W L bits arity ambient i:=by
  by_cases h:∃ j,port j=i
  · obtain ⟨j,rfl⟩:=h
    rw [slots,Function.comp_apply,remap_port,bank,Fin.addCases_left,input,old,Fin.addCases_left]
    exact (hf j).trans (input_port P H V C T core W L bits arity ambient j).symm
  · have hi:∀ j,port j≠i:=by simpa using h
    rw [slots,Function.comp_apply,remap_other i hi,bank,Fin.addCases_right,input,Fin.addCases_right]
    exact (input_outside P H V C T core W L bits arity ambient i hi).symm

theorem heads_local {t : ℕ} (fields : Fin 104→Fin t) (cursor : Fin t→ℕ)
    (hf : ∀ j,cursor (fields j)=cursors j) (i : Fin 3243) :
    heads cursor (slots fields i)=FamilyPrepare.heads FamilyHeads.heads i:=by
  by_cases h:∃ j,port j=i
  · obtain ⟨j,rfl⟩:=h
    rw [slots,Function.comp_apply,remap_port,bank,Fin.addCases_left,heads,old,Fin.addCases_left]
    exact (hf j).trans (head_port j).symm
  · have hi:∀ j,port j≠i:=by simpa using h
    rw [slots,Function.comp_apply,remap_other i hi,bank,Fin.addCases_right,heads,Fin.addCases_right]
    exact (head_outside i hi).symm

theorem outside {t : ℕ} (fields : Fin 104→Fin t) (i : Fin t) (hi : ∀ j,fields j≠i) :
    ∀ j,slots fields j≠old i:=by
  have away:∀ z,bank fields z≠old i:=by
    intro z
    refine Fin.addCases (m:=104) (n:=3243) (fun j=>?_) (fun j=>?_) z
    · intro he
      have hv:=congrArg Fin.val he
      simp only [bank,Fin.addCases_left,old,Fin.val_castAdd] at hv
      exact hi j (Fin.ext hv)
    · intro he
      have hv:=congrArg Fin.val he
      simp only [bank,Fin.addCases_right,old,Fin.val_castAdd,Fin.val_natAdd] at hv
      have ht:=i.isLt
      omega
  exact fun j=>away (remap j)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCold.Call
