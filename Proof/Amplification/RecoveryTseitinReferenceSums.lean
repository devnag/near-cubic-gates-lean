import Proof.Amplification.RecoveryTseitinReference

/-! Physically compute the target and two gate-reference offsets from the
retained raw arity, node position and original operands. The unshifted first
operand is retained for a free-input node. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinReferences
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (arity index left right : Nat) : Fin 10→List Bool :=
  ![List.replicate arity true,List.replicate index true,List.replicate left true,List.replicate right true,
    [],[],[],[],[],[]]
def slots : Fin 3→Fin 4→Fin 10 := ![![0,1,4,5],![0,2,6,7],![0,3,8,9]]
theorem injective (i : Fin 3) : Function.Injective (slots i) := by fin_cases i <;> decide
noncomputable def part (i : Fin 3) := RecoveryFocus.machine (slots i) ClockUnarySum.machine
noncomputable def sumsMachine := Composition.machine (Composition.machine (part 0) (part 1)) (part 2)
def cell (arity index : Nat) : Fin 4→List Bool :=
  ![List.replicate arity true,List.replicate index true,List.replicate (arity+index) true,
    List.replicate (arity+index+2) false]
noncomputable def first (arity index left right : Nat) := install (slots 0) (input arity index left right) (cell arity index)
noncomputable def second (arity index left right : Nat) := install (slots 1) (first arity index left right) (cell arity left)
noncomputable def output (arity index left right : Nat) := install (slots 2) (second arity index left right) (cell arity right)
def budget (arity index left right : Nat) := 6*arity+2*index+2*left+2*right+20

theorem first_other (arity index left right : Nat) (i : Fin 10)
    (hi : i≠0 ∧ i≠1 ∧ i≠4 ∧ i≠5) : first arity index left right i=input arity index left right i := by
  apply install_other
  intro j
  fin_cases j <;> simp only [slots] <;> exact Ne.symm (by tauto)
theorem second_other (arity index left right : Nat) (i : Fin 10)
    (hi : i≠0 ∧ i≠2 ∧ i≠6 ∧ i≠7) : second arity index left right i=first arity index left right i := by
  apply install_other
  intro j
  fin_cases j <;> simp only [slots] <;> exact Ne.symm (by tauto)

theorem sums_run (arity index left right : Nat) :
    ClockJoin.ReadyRun sumsMachine (budget arity index left right) (input arity index left right)
      (output arity index left right) := by
  have h0 := (show ClockJoin.ReadyRun ClockUnarySum.machine (2*(arity+index)+6)
    ![List.replicate arity true,List.replicate index true,[],[]] (cell arity index) from
    ClockUnarySum.sum_ready arity index).focus
      (slots 0) (injective 0) (input arity index left right) (by intro j; fin_cases j <;> rfl)
  have h1 := (show ClockJoin.ReadyRun ClockUnarySum.machine (2*(arity+left)+6)
    ![List.replicate arity true,List.replicate left true,[],[]] (cell arity left) from
    ClockUnarySum.sum_ready arity left).focus
      (slots 1) (injective 1) (first arity index left right) (by
        intro j; fin_cases j
        · exact install_slot (slots 0) (injective 0) _ _ 0
        all_goals rw [first_other _ _ _ _ _ (by decide)]; rfl)
  have h2 := (show ClockJoin.ReadyRun ClockUnarySum.machine (2*(arity+right)+6)
    ![List.replicate arity true,List.replicate right true,[],[]] (cell arity right) from
    ClockUnarySum.sum_ready arity right).focus
      (slots 2) (injective 2) (second arity index left right) (by
        intro j; fin_cases j
        · exact install_slot (slots 1) (injective 1) _ _ 0
        all_goals rw [second_other _ _ _ _ _ (by decide),first_other _ _ _ _ _ (by decide)]; rfl)
  have hwhole := ClockJoin.join (Composition.machine (part 0) (part 1)) (part 2) _ _ _ _ _
    (ClockJoin.join (part 0) (part 1) _ _ _ _ _ h0 h1) h2
  have he : ((2*(arity+index)+6)+1+(2*(arity+left)+6))+1+(2*(arity+right)+6)=budget arity index left right := by
    unfold budget
    omega
  rw [he] at hwhole
  exact hwhole

theorem output_fields (arity index left right : Nat) :
    output arity index left right 4=List.replicate (arity+index) true ∧
    output arity index left right 2=List.replicate left true ∧
    output arity index left right 6=List.replicate (arity+left) true ∧
    output arity index left right 8=List.replicate (arity+right) true := by
  have o4 : output arity index left right 4=second arity index left right 4 := install_other _ _ _ _ (by decide)
  have o2 : output arity index left right 2=second arity index left right 2 := install_other _ _ _ _ (by decide)
  have o6 : output arity index left right 6=second arity index left right 6 := install_other _ _ _ _ (by decide)
  refine ⟨?_,?_,?_,?_⟩
  · rw [o4,second_other _ _ _ _ _ (by decide)]
    exact install_slot (slots 0) (injective 0) _ _ 2
  · rw [o2]
    exact install_slot (slots 1) (injective 1) _ _ 1
  · rw [o6]
    exact install_slot (slots 1) (injective 1) _ _ 2
  · exact install_slot (slots 2) (injective 2) _ _ 2

end NearCubicWires.RepairSource.RecoveryTseitinReferences
