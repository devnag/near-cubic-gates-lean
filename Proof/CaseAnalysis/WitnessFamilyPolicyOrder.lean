import Proof.CaseAnalysis.WitnessFamilyPolicyPorts
import Proof.CaseAnalysis.WitnessFamilyCallRun

/-! The exact fixed family port order combines the four retained external
words P/H/V/raw with the six legal-policy words and existing mass store. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyPolicyPorts
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def smallOrder : Fin 10→Fin 10:=![0,4,6,7,1,5,8,2,9,3]
def order : Fin 104→Fin (4+100):=
  Fin.addCases (m:=10) (n:=94) (motive:=fun _=>Fin (4+100))
    (fun i=>(smallOrder i).castAdd 94) (fun i=>i.natAdd 10)
theorem order_injective : Function.Injective order:=by
  apply RecoveryColdAllCode.join_injective
  · intro i j he
    have hv:=congrArg Fin.val he
    have inj:Function.Injective smallOrder:=by decide
    exact inj (Fin.ext hv)
  · intro i j he
    have hv:=congrArg Fin.val he
    change 10+i.val=10+j.val at hv
    exact Fin.ext (by omega)
  · intro i j he
    have hv:=congrArg Fin.val he
    change (smallOrder i).val=10+j.val at hv
    have ht:=(smallOrder i).isLt
    omega

def externalValues (P H V : ℕ) (bits : List Bool) : Fin 4→List Bool:=
  ![List.replicate P true,List.replicate H true,List.replicate V true,frame bits]
def localValues (core W L T b : ℕ) (arity : List Bool) (ambient : Fin 94→List Bool) : Fin 100→List Bool:=
  Fin.addCases (m:=6) (n:=94) (motive:=fun _=>List Bool)
    (![UnaryTemplate.tape core,frame arity,List.replicate W true,List.replicate L true,
      List.replicate T true,List.replicate b true] : Fin 6→List Bool) ambient

theorem values_order (P H V C T core W L : ℕ) (bits arity : List Bool) (ambient : Fin 94→List Bool)
    (i : Fin 104) : Fin.addCases (m:=4) (n:=100) (motive:=fun _=>List Bool)
      (externalValues P H V bits) (localValues core W L T (natBitLength C) arity ambient) (order i)=
      FamilySparse.values P H V C T core W L bits arity ambient i:=by
  refine Fin.addCases (m:=10) (n:=94) (fun j=>?_) (fun j=>?_) i
  · fin_cases j <;> rfl
  · rw [order,Fin.addCases_right]
    have he:j.natAdd 10=(j.natAdd 6).natAdd 4:=by apply Fin.ext;change 10+j.val=4+(6+j.val);omega
    simp only [FamilySparse.values,Fin.addCases_right]
    rw [he,Fin.addCases_right,localValues,Fin.addCases_right]

theorem local_values (e den : ℕ) (delta : ℚ) (copies : ℕ) (sym : Bool) (R q0 cb b : ℕ)
    (data : Fin (LegalTemplate.tapes e)→List Bool)
    (hf : LegalTemplate.Call.Fields e den delta copies sym R q0 cb b data) (i : Fin 100) :
    data (port e i)=localValues R (LegalPolicy.W e den R)
      (DescriptionPolicy.value sym R q0 (LegalPolicy.W e den R)) (LegalPolicy.T delta copies q0 cb) b
      (SignedSortKey.binary (natBitLength R) R) (LegalTemplate.project e data) i:=by
  refine Fin.addCases (m:=6) (n:=94) (fun j=>?_) (fun j=>?_) i
  · fin_cases j
    · exact hf.domain
    · exact hf.arity
    · exact hf.wire
    · exact hf.description
    · exact hf.terms
    · exact hf.width
  · simp only [port,localValues,Fin.addCases_right,mass,LegalTemplate.project]

def join {t : ℕ} (external : Fin 4→Fin t) (inside : Fin 100→Fin t) : Fin 104→Fin t:=
  (Fin.addCases (m:=4) (n:=100) (motive:=fun _=>Fin t) external inside) ∘ order

theorem join_injective {t : ℕ} (external : Fin 4→Fin t) (inside : Fin 100→Fin t)
    (he : Function.Injective external) (hi : Function.Injective inside)
    (disjoint : ∀ i j,external i≠inside j) : Function.Injective (join external inside):=
  (RecoveryColdAllCode.join_injective external inside he hi disjoint).comp order_injective

theorem join_values {t : ℕ} (external : Fin 4→Fin t) (inside : Fin 100→Fin t) (data : Fin t→List Bool)
    (P H V C T core W L : ℕ) (bits arity : List Bool) (ambient : Fin 94→List Bool)
    (he : ∀ i,data (external i)=externalValues P H V bits i)
    (hi : ∀ i,data (inside i)=localValues core W L T (natBitLength C) arity ambient i) (i : Fin 104) :
    data (join external inside i)=FamilySparse.values P H V C T core W L bits arity ambient i:=by
  have hb (j : Fin (4+100)) : data (Fin.addCases external inside j)=
      Fin.addCases (externalValues P H V bits) (localValues core W L T (natBitLength C) arity ambient) j:=by
    refine Fin.addCases (m:=4) (n:=100) (fun k=>?_) (fun k=>?_) j
    · simpa only [Fin.addCases_left] using he k
    · simpa only [Fin.addCases_right] using hi k
  exact (hb (order i)).trans (values_order P H V C T core W L bits arity ambient i)

theorem join_heads {t : ℕ} (external : Fin 4→Fin t) (inside : Fin 100→Fin t) (cursor : Fin t→ℕ)
    (he : ∀ i,cursor (external i)=0) (hi : ∀ i,cursor (inside i)=if i.val=0 then 1 else 0) (i : Fin 104) :
    cursor (join external inside i)=FamilySparse.cursors i:=by
  refine Fin.addCases (m:=10) (n:=94) (fun j=>?_) (fun j=>?_) i
  · fin_cases j
    all_goals first
      | exact he _
      | exact hi _
  · have hport:join external inside (j.natAdd 10)=inside (j.natAdd 6):=by
      simp only [join,Function.comp_apply,order,Fin.addCases_right]
      have he':j.natAdd 10=(j.natAdd 6).natAdd 4:=by apply Fin.ext;change 10+j.val=4+(6+j.val);omega
      rw [he',Fin.addCases_right]
    rw [hport,hi]
    simp only [Fin.val_natAdd,if_neg (show 6+j.val≠0 by omega),FamilySparse.cursors,
      if_neg (show 10+j.val≠1 by omega)]

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyPolicyPorts
