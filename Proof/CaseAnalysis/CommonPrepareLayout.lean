import Proof.CaseAnalysis.CapacityBudget
import Proof.CaseAnalysis.HierarchyRequestShared

/-! Sparse common-prefix ports. Capacity consumes the final address and the
original hierarchy request consumes the genuine refuter answer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCommonPrepare
open LocalBitMultitape RepairSource RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (k : ℕ):=CloseoutHierarchyRequest.Shared.tapes k 27
def capacityLocal (i : Fin 26) : Fin 27:=
  if i.val=0 then 0 else ⟨i.val+1,by have hi:=i.isLt;omega⟩
def capacitySlots (k : ℕ) (i : Fin 26) : Fin (tapes k):=
  CloseoutHierarchyRequest.Shared.old k (capacityLocal i)
def requestSlots (k : ℕ):=CloseoutHierarchyRequest.Shared.bank k (1 : Fin 27)
def addressSlot (k : ℕ) : Fin (tapes k):=CloseoutHierarchyRequest.Shared.old k (0 : Fin 27)
def answerSlot (k : ℕ) : Fin (tapes k):=CloseoutHierarchyRequest.Shared.old k (1 : Fin 27)
def capacitySlot (k : ℕ):=capacitySlots k 24
def hierarchySlot (k : ℕ):=requestSlots k (CloseoutHierarchyRequest.fresh k 0)
def ambient (address answer : List Bool) (i : Fin 27):=
  if i.val=0 then frame address else if i.val=1 then frame answer else []
def input (k : ℕ) (address answer : List Bool):=CloseoutHierarchyRequest.Shared.input k (ambient address answer)

theorem capacity_local_injective : Function.Injective capacityLocal:=by
  intro i j he
  have hv:=congrArg Fin.val he
  apply Fin.ext
  dsimp only [capacityLocal] at hv
  split_ifs at hv <;>dsimp at hv <;>omega
theorem capacity_injective (k : ℕ) : Function.Injective (capacitySlots k):=by
  intro i j he
  apply capacity_local_injective
  exact Fin.ext (congrArg (fun x : Fin (tapes k)=>x.val) he)
theorem capacity_ne_answer (i : Fin 26) : capacityLocal i≠1:=by
  intro he
  have hv:=congrArg Fin.val he
  dsimp only [capacityLocal] at hv
  split_ifs at hv <;>dsimp at hv <;>omega
theorem disjoint (k : ℕ) (i : Fin 26) (j : Fin (CloseoutHierarchyRequest.tapes k)) :
    capacitySlots k i≠requestSlots k j:=
  Ne.symm (CloseoutHierarchyRequest.Shared.bank_other k (1 : Fin 27) (capacityLocal i)
    (capacity_ne_answer i) j)

def first (k A B0 : ℕ):=RecoveryFocus.machine (capacitySlots k) (CloseoutCapacity.machine A B0)
def last (k CH : ℕ):=CloseoutHierarchyRequest.Shared.machine k CH (1 : Fin 27)
def machine (k CH A B0 : ℕ):=Composition.machine (first k A B0) (last k CH)
def budget (k CH A B0 : ℕ) (address answer : List Bool):=
  CloseoutCapacity.budget A B0 address+1+CloseoutHierarchyRequest.budget k CH answer

theorem capacity_input (k : ℕ) (address answer : List Bool) (i : Fin 26) :
    input k address answer (capacitySlots k i)=CloseoutCapacity.input address i:=by
  simp only [input,capacitySlots,CloseoutHierarchyRequest.Shared.input,
    CloseoutHierarchyRequest.Shared.old,Fin.addCases_left]
  by_cases hi : i.val=0
  · simp [capacityLocal,hi,ambient,CloseoutCapacity.input]
  · simp [capacityLocal,hi,ambient,CloseoutCapacity.input]

theorem request_input (k : ℕ) (address answer : List Bool)
    (j : Fin (CloseoutHierarchyRequest.tapes k)) :
    input k address answer (requestSlots k j)=CloseoutHierarchyRequest.input k answer j:=by
  rw [CloseoutHierarchyRequest.input_lookup]
  by_cases hj : j.val=2
  · simp only [requestSlots,CloseoutHierarchyRequest.Shared.bank,if_pos hj,input,
      CloseoutHierarchyRequest.Shared.input,CloseoutHierarchyRequest.Shared.old,Fin.addCases_left]
    rfl
  · simp only [requestSlots,CloseoutHierarchyRequest.Shared.bank,if_neg hj,input,
      CloseoutHierarchyRequest.Shared.input,Fin.addCases_right]

end
end NearCubicWires.RepairOrdinary.CloseoutCommonPrepare
