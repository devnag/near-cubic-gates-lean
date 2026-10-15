import Proof.CaseAnalysis.CapacityPower
import Proof.Hierarchy.HierarchyAllocation

/-! One fixed cold producer for the shared recovery capacity 2^(A*n+B).
Its only input is the actual final-language word. Constants, input-length
arithmetic, exponential output and head resets are all executed. -/
namespace NearCubicWires.RepairSource.CloseoutCapacity
open LocalBitMultitape RepairOrdinary RecoveryRootRound VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def allocationSlots : Fin 10→Fin 26 := fun i=>i.castAdd 16
def powerSlots : Fin 17→Fin 26 := fun i=>
  ⟨if i.val=0 then 8 else i.val+9,by have:=i.isLt;split_ifs <;> omega⟩
theorem allocation_injective : Function.Injective allocationSlots := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 26=>i.val) h)
theorem power_injective : Function.Injective powerSlots := by
  intro a b h
  have hv:=congrArg Fin.val h
  apply Fin.ext
  dsimp only [powerSlots] at hv
  split_ifs at hv <;> omega
def allocation (A B : Nat) := RecoveryFocus.machine allocationSlots (HierarchyAllocation.machine A B)
def power := RecoveryFocus.machine powerSlots Power.machine
def machine (A B : Nat) := Composition.machine (allocation A B) power
def input (bits : List Bool) : Fin 26→List Bool := fun i=>if i.val=0 then frame bits else []
def budget (A B : Nat) (bits : List Bool) :=
  HierarchyAllocation.budget A B bits+1+Power.budget (A*bits.length+B)
def capacity (A B n : Nat) := 2^(A*n+B)

theorem capacity_run (A B : Nat) (bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun (machine A B) (budget A B bits) (input bits) out ∧
      out 24=List.replicate (capacity A B bits.length) true ∧
      out 22=UnaryTemplate.tape (capacity A B bits.length) ∧ out 0=frame bits := by
  have ha:=(HierarchyAllocation.allocation_ready A B bits).focus
    allocationSlots allocation_injective (input bits) (by intro i;rfl)
  let middle:=install allocationSlots (input bits) (HierarchyAllocation.output A B bits)
  change ClockJoin.ReadyRun (allocation A B) (HierarchyAllocation.budget A B bits)
    (input bits) middle at ha
  obtain ⟨powerOut,hp,hn,ht⟩:=Power.power_run (A*bits.length+B)
  have hf:=hp.focus powerSlots power_injective middle (by
    intro i
    fin_cases i
    · change install allocationSlots _ _ (allocationSlots 8)=_
      rw [install_slot _ allocation_injective]
      rfl
    all_goals
      dsimp only [middle]
      rw [install_other _ _ _ _ (by
        intro j hj
        have hv:=congrArg Fin.val hj
        have:=j.isLt
        dsimp [allocationSlots,powerSlots] at hv
        omega)]
      rfl)
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ ha hf,?_,?_,?_⟩
  · change install powerSlots _ _ (powerSlots 15)=_
    rw [install_slot _ power_injective]
    exact hn
  · change install powerSlots _ _ (powerSlots 13)=_
    rw [install_slot _ power_injective]
    exact ht
  · rw [install_other _ _ _ _ (by
      intro j hj
      have hv:=congrArg Fin.val hj
      dsimp [powerSlots] at hv
      split_ifs at hv)]
    change install allocationSlots _ _ (allocationSlots 0)=_
    rw [install_slot _ allocation_injective]
    rfl

end
end NearCubicWires.RepairSource.CloseoutCapacity
