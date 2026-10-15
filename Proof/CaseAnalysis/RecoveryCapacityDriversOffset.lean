import Proof.Hierarchy.HierarchyAllocation
import Proof.CaseAnalysis.CaseTwoLayout

/-! Add a fixed paid offset to a raw unary capacity, then allocate its
reusable false scratch and reset log. Every input head is restored. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCapacityDrivers.Offset
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def constantSlots : Fin 2→Fin 7:=![1,2]
def sumSlots : Fin 4→Fin 7:=![0,1,3,4]
def eraseSlots : Fin 3→Fin 7:=![5,3,6]
def constant (J : ℕ):=RecoveryFocus.machine constantSlots
  (HierarchyFixedWord.machine (List.replicate J true))
def sum:=RecoveryFocus.machine sumSlots ClockUnarySum.machine
def erase:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1)
def machine (J : ℕ):=Composition.machine (Composition.machine (constant J) sum) erase
def budget (J n : ℕ):=2*J+2+1+(2*(n+J)+6)+1+(2*(n+J)+4)
def input (n : ℕ) : Fin 7→List Bool:=![List.replicate n true,[],[],[],[],[],[]]
def constants (J n : ℕ) : Fin 7→List Bool:=
  ![List.replicate n true,List.replicate J true,List.replicate J false,[],[],[],[]]
def summed (J n : ℕ) : Fin 7→List Bool:=
  ![List.replicate n true,List.replicate J true,List.replicate J false,
    List.replicate (n+J) true,List.replicate (n+J+2) false,[],[]]

theorem constants_run (J n : ℕ) : ClockJoin.ReadyRun (constant J) (2*J+2) (input n) (constants J n):=by
  obtain ⟨r,hr,ht,hh,hs⟩:=HierarchyFixedWord.word_ready (List.replicate J true)
  simp only [List.length_replicate] at hr ht hs
  have h:=(show ClockJoin.ReadyRun _ _ _ _ from ⟨r,hr,ht,hh,hs.le⟩).focus
    constantSlots (by decide) (input n) (by intro j;fin_cases j <;>rfl)
  have he : install constantSlots (input n)
      (![List.replicate J true,List.replicate J false] : Fin 2→List Bool)=constants J n:=by
    apply HierarchyAllocation.install_eq constantSlots (by decide)
    · intro j;fin_cases j <;>rfl
    · intro i hi;fin_cases i
      all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl)
  rw [he] at h
  exact h

theorem sum_run (J n : ℕ) : ClockJoin.ReadyRun sum (2*(n+J)+6) (constants J n) (summed J n):=by
  have h:=(ClockUnarySum.sum_ready n J).focus sumSlots (by decide) (constants J n)
    (by intro j;fin_cases j <;>rfl)
  have he : install sumSlots (constants J n)
      (![List.replicate n true,List.replicate J true,List.replicate (n+J) true,
        List.replicate (n+J+2) false] : Fin 4→List Bool)=summed J n:=by
    apply HierarchyAllocation.install_eq sumSlots (by decide)
    · intro j;fin_cases j <;>rfl
    · intro i hi;fin_cases i
      all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) |
        exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl)
  rw [he] at h
  exact h

theorem erase_run (J n : ℕ) : ∃ out,
    ClockJoin.ReadyRun erase (2*(n+J)+4) (summed J n) out ∧
    out 0=List.replicate n true ∧ out 3=List.replicate (n+J) true ∧
    out 5=List.replicate (n+J) false ∧ out 6=List.replicate (n+J+1) false:=by
  have h:=(CloseoutCaseTwo.Cold.erase_ready 1 (n+J)).focus eraseSlots (by decide) (summed J n)
    (by intro j;fin_cases j <;>simp [summed,eraseSlots,CloseoutCaseTwo.Cold.eraseInput] <;>rfl)
  refine ⟨_,h,?_,?_,?_,?_⟩
  · exact install_other eraseSlots (summed J n) (CloseoutCaseTwo.Cold.eraseOutput 1 (n+J)) 0 (by decide)
  · exact install_slot eraseSlots (by decide) (summed J n) (CloseoutCaseTwo.Cold.eraseOutput 1 (n+J)) 1
  · exact install_slot eraseSlots (by decide) (summed J n) (CloseoutCaseTwo.Cold.eraseOutput 1 (n+J)) 0
  · exact install_slot eraseSlots (by decide) (summed J n) (CloseoutCaseTwo.Cold.eraseOutput 1 (n+J)) 2

theorem run (J n : ℕ) : ∃ out,ClockJoin.ReadyRun (machine J) (budget J n) (input n) out ∧
    out 0=List.replicate n true ∧ out 3=List.replicate (n+J) true ∧
    out 5=List.replicate (n+J) false ∧ out 6=List.replicate (n+J+1) false:=by
  obtain ⟨out,hr,h0,h3,h5,h6⟩:=erase_run J n
  exact ⟨out,ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ (constants_run J n) (sum_run J n)) hr,h0,h3,h5,h6⟩

end
end NearCubicWires.RepairOrdinary.RecoveryCapacityDrivers.Offset
