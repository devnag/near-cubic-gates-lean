import Proof.CaseAnalysis.WitnessFamilySparse

/-! The exact live entry ports of the existing family machine. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilySparse
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def port : Fin 104→Fin 3243:=Fin.addCases (m:=10) (n:=94) (motive:=fun _=>Fin 3243) headerSlot massSlot
def values (P H V C T core W L : ℕ) (bits arity : List Bool) (ambient : Fin 94→List Bool) : Fin 104→List Bool:=
  Fin.addCases (m:=10) (n:=94) (motive:=fun _=>List Bool) (headers P H V C T core W L bits arity) ambient
def cursors (i : Fin 104) : ℕ:=if i.val=1 then 1 else 0

theorem header_injective : Function.Injective headerSlot:=by decide
private theorem header_away (i : Fin 10) : (headerSlot i).val<725 ∨ 819 ≤ (headerSlot i).val:=by
  fin_cases i <;> decide

theorem port_injective : Function.Injective port:=by
  intro i j h
  revert j h
  refine Fin.addCases (m:=10) (n:=94) (fun i=>?_) (fun i=>?_) i
  · intro j
    refine Fin.addCases (m:=10) (n:=94) (fun j h=>?_) (fun j h=>?_) j
    · simp only [port,Fin.addCases_left] at h
      have he:headerSlot i=headerSlot j:=h
      exact congrArg (Fin.castAdd 94) (header_injective he)
    · have hv:=congrArg Fin.val h
      simp only [port,Fin.addCases_left,Fin.addCases_right] at hv
      change (headerSlot i).val=725+j.val at hv
      rcases header_away i with hlt|hle <;> omega
  · intro j
    refine Fin.addCases (m:=10) (n:=94) (fun j h=>?_) (fun j h=>?_) j
    · have hv:=congrArg Fin.val h
      simp only [port,Fin.addCases_left,Fin.addCases_right] at hv
      change 725+i.val=(headerSlot j).val at hv
      rcases header_away j with hlt|hle <;> omega
    · have hv:=congrArg Fin.val h
      simp only [port,Fin.addCases_right] at hv
      change 725+i.val=725+j.val at hv
      exact congrArg (Fin.natAdd 10) (Fin.ext (by omega))

theorem input_port (P H V C T core W L : ℕ) (bits arity : List Bool) (ambient : Fin 94→List Bool)
    (i : Fin 104) : FamilyCold.input P H V C T core W L bits arity ambient (port i)=
      values P H V C T core W L bits arity ambient i:=by
  refine Fin.addCases (m:=10) (n:=94) (fun j=>?_) (fun j=>?_) i
  · fin_cases j <;> rfl
  · simp only [port,values,Fin.addCases_right]
    exact store_tape P H V C T core W L bits arity ambient j

theorem input_outside (P H V C T core W L : ℕ) (bits arity : List Bool) (ambient : Fin 94→List Bool)
    (i : Fin 3243) (hi : ∀ j,port j≠i) : FamilyCold.input P H V C T core W L bits arity ambient i=[]:=by
  rw [input_eq]
  have hm:¬(725 ≤ i.val ∧ i.val<819):=by
    intro h
    let j : Fin 94:=⟨i.val-725,by omega⟩
    apply hi (j.natAdd 10)
    simp only [port,Fin.addCases_right]
    apply Fin.ext
    change 725+(i.val-725)=i.val
    omega
  have hn (j : Fin 10):i.val≠(headerSlot j).val:=by
    intro h
    apply hi (j.castAdd 94)
    simp only [port,Fin.addCases_left]
    exact Fin.ext h.symm
  have h720:i.val≠720:=hn 0
  have h2501:i.val≠2501:=hn 1
  have h2525:i.val≠2525:=hn 2
  have h2526:i.val≠2526:=hn 3
  have h2530:i.val≠2530:=hn 4
  have h3034:i.val≠3034:=hn 5
  have h3035:i.val≠3035:=hn 6
  have h3238:i.val≠3238:=hn 7
  have h3241:i.val≠3241:=hn 8
  have h3242:i.val≠3242:=hn 9
  simp only [data,dif_neg hm,if_neg h720,if_neg h2501,if_neg h2525,if_neg h2526,if_neg h2530,if_neg h3034,if_neg h3035,if_neg h3238,if_neg h3241,if_neg h3242]

theorem head_shape (i : Fin 3243) : FamilyPrepare.heads FamilyHeads.heads i=if i.val=2501 then 1 else 0:=by
  refine Fin.addCases (m:=3241) (n:=2) (fun j=>?_) (fun j=>?_) i
  · simp only [FamilyPrepare.heads,Fin.addCases_left,Fin.val_castAdd]
    exact FamilyHeads.shape j
  · have hn:3241+j.val≠2501:=by omega
    simp only [FamilyPrepare.heads,Fin.addCases_right,Fin.val_natAdd,if_neg hn]

theorem head_port (i : Fin 104) : FamilyPrepare.heads FamilyHeads.heads (port i)=cursors i:=by
  rw [head_shape]
  refine Fin.addCases (m:=10) (n:=94) (fun j=>?_) (fun j=>?_) i
  · fin_cases j <;> rfl
  · have hn:725+j.val≠2501:=by omega
    have hn':10+j.val≠1:=by omega
    simp only [port,Fin.addCases_right,massSlot,cursors,Fin.val_natAdd,if_neg hn,if_neg hn']

theorem head_outside (i : Fin 3243) (hi : ∀ j,port j≠i) : FamilyPrepare.heads FamilyHeads.heads i=0:=by
  rw [head_shape]
  have hn:i.val≠2501:=by
    intro h
    exact hi ((1 : Fin 10).castAdd 94) (Fin.ext h.symm)
  exact if_neg hn

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilySparse
