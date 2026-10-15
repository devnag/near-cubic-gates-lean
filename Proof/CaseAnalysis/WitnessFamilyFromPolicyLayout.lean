import Proof.CaseAnalysis.WitnessFamilyPolicyOrder
import Proof.CaseAnalysis.WitnessFamilyCapacityJoin

/-! The actual paid P/H outputs and existing legal-policy ports feed one
whole-family call. The raw family and actual V remain separate old tapes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyFromPolicy
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable {t : ℕ}
def external (E : ℕ) (source count raw : Fin t) : Fin 4→Fin (t+FamilyCapacity.Call.extra E):=
  ![FamilyCapacity.Call.slots E source (FamilyCapacity.pSlot E),
    FamilyCapacity.Call.slots E source (FamilyCapacity.hSlot E),
    FamilyCapacity.Call.old E count,FamilyCapacity.Call.old E raw]
def inside (e E : ℕ) (policy : Fin (LegalTemplate.tapes e)→Fin t) (i : Fin 100):=
  FamilyCapacity.Call.old E (policy (FamilyPolicyPorts.port e i))
def fields (e E : ℕ) (source count raw : Fin t) (policy : Fin (LegalTemplate.tapes e)→Fin t):=
  FamilyPolicyPorts.join (external E source count raw) (inside e E policy)

theorem external_val (E : ℕ) (source count raw : Fin t) (i : Fin 4) :
    (external E source count raw i).val=(![t+(5+2*E),t+(FamilyCapacity.A E+4),count.val,raw.val] : Fin 4→ℕ) i:=by
  have hH:(FamilyCapacity.hSlot E).val=FamilyCapacity.A E+4:=rfl
  fin_cases i
  · change (FamilyCapacity.Call.slots E source (FamilyCapacity.pSlot E)).val=t+(5+2*E)
    simp only [FamilyCapacity.Call.slots,FamilyCapacity.p_val,if_neg (show 5+2*E≠0 by omega),Fin.val_natAdd]
  · change (FamilyCapacity.Call.slots E source (FamilyCapacity.hSlot E)).val=t+(FamilyCapacity.A E+4)
    simp only [FamilyCapacity.Call.slots,hH,if_neg (show FamilyCapacity.A E+4≠0 by omega),Fin.val_natAdd]
  all_goals rfl

theorem external_injective (E : ℕ) (source count raw : Fin t) (hne : count≠raw) :
    Function.Injective (external E source count raw):=by
  intro i j he
  have hv:=congrArg Fin.val he
  rw [external_val,external_val] at hv
  have ha:FamilyCapacity.A E=14+2*E:=rfl
  have hc:=count.isLt
  have hr:=raw.isLt
  have hne':count.val≠raw.val:=fun h=>hne (Fin.ext h)
  fin_cases i <;> fin_cases j <;> first | rfl | (dsimp at hv;omega)

theorem inside_injective (e E : ℕ) (policy : Fin (LegalTemplate.tapes e)→Fin t)
    (hp : Function.Injective policy) : Function.Injective (inside e E policy):=by
  intro i j he
  have hv:=congrArg Fin.val he
  have eq:policy (FamilyPolicyPorts.port e i)=policy (FamilyPolicyPorts.port e j):=Fin.ext hv
  exact FamilyPolicyPorts.port_injective e (hp eq)

theorem fields_injective (e E : ℕ) (source count raw : Fin t) (policy : Fin (LegalTemplate.tapes e)→Fin t)
    (hp : Function.Injective policy) (hne : count≠raw)
    (hc : ∀ i,count≠policy i) (hr : ∀ i,raw≠policy i) : Function.Injective (fields e E source count raw policy):=by
  apply FamilyPolicyPorts.join_injective _ _ (external_injective E source count raw hne) (inside_injective e E policy hp)
  intro i j he
  have hv:=congrArg Fin.val he
  rw [external_val] at hv
  have hj:=(policy (FamilyPolicyPorts.port e j)).isLt
  change (![t+(5+2*E),t+(FamilyCapacity.A E+4),count.val,raw.val] : Fin 4→ℕ) i=
    (policy (FamilyPolicyPorts.port e j)).val at hv
  fin_cases i
  · dsimp at hv;omega
  · dsimp at hv;omega
  · exact hc _ (Fin.ext hv)
  · exact hr _ (Fin.ext hv)

def first (E K : ℕ) (source : Fin t):=
  TapeEmbedding.machine FamilyCold.Call.extra (FamilyCapacity.Call.machine E K source)
def second (e E : ℕ) (source count raw : Fin t) (policy : Fin (LegalTemplate.tapes e)→Fin t)
    (sym : Bool) (k : ℕ) (q : ℚ):=
  FamilyCold.Call.machine sym k q (fields e E source count raw policy)
def machine (e E K : ℕ) (source count raw : Fin t) (policy : Fin (LegalTemplate.tapes e)→Fin t)
    (sym : Bool) (k : ℕ) (q : ℚ):=
  Composition.machine (first E K source) (second e E source count raw policy sym k q)
def input (E : ℕ) (data : Fin t→List Bool):=FamilyCold.Call.input (FamilyCapacity.Call.input E data)
def heads (E : ℕ) (cursor : Fin t→ℕ):=FamilyCold.Call.heads (FamilyCapacity.Call.heads E cursor)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyFromPolicy
