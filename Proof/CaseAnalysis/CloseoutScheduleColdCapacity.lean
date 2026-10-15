import Proof.CaseAnalysis.ScheduleLayout

/-! The existing cold C producer feeds the actual schedule erase driver,
preserving the language input and every unallocated schedule/metadata port. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Cold
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def input (w : Nat) (bits : List Bool) : Fin (tapes w) → List Bool :=
  fun i => if i.val=w+6 then frame bits else []
def capacityProgram (w A B : Nat) := RecoveryFocus.machine (capacitySlots w) (CloseoutCapacity.machine A B)

theorem capacity_core_ne (w : Nat) (i : Fin (w+6)) (hi : i.val ≠ w+3) (j : Fin 26) :
    capacitySlots w j ≠ core w i := by
  intro h
  have hv := congrArg Fin.val h
  have := i.isLt
  by_cases hj : j.val=24 <;> simp [capacitySlots,hj,port,core,extra] at hv <;> omega
theorem capacity_extra_ne (w : Nat) (i : Fin 30) (hi : 26 ≤ i.val) (j : Fin 26) :
    capacitySlots w j ≠ extra w i := by
  intro h
  have hv := congrArg Fin.val h
  have := j.isLt
  by_cases hj : j.val=24 <;> simp [capacitySlots,hj,port,core,extra] at hv <;> omega

theorem capacity_run (w A B : Nat) (bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun (capacityProgram w A B) (CloseoutCapacity.budget A B bits) (input w bits) out ∧
    out (port w 3) = List.replicate (CloseoutCapacity.capacity A B bits.length) true ∧
    out (extra w 0) = frame bits ∧
    (∀ i : Fin (w+6), i.val ≠ w+3 → out (core w i) = []) ∧
    (∀ i : Fin 30, 26 ≤ i.val → out (extra w i) = []) := by
  obtain ⟨a,ha,hC,_,hx⟩ := CloseoutCapacity.capacity_run A B bits
  have hf := ha.focus (capacitySlots w) (capacity_injective w) (input w bits) (by
    intro i
    by_cases hi : i.val=24
    · simp [input,capacitySlots,hi,port,core,CloseoutCapacity.input]
    · simp [input,capacitySlots,hi,extra,CloseoutCapacity.input])
  refine ⟨_,hf,?_,?_,?_,?_⟩
  · change install (capacitySlots w) (input w bits) a (capacitySlots w 24) = _
    rw [install_slot _ (capacity_injective w)]
    exact hC
  · change install (capacitySlots w) (input w bits) a (capacitySlots w 0) = _
    rw [install_slot _ (capacity_injective w)]
    exact hx
  · intro i hi
    rw [install_other _ _ _ _ (capacity_core_ne w i hi)]
    have hlt := i.isLt
    simp [input,core,show i.val ≠ w+6 by omega]
  · intro i hi
    rw [install_other _ _ _ _ (capacity_extra_ne w i hi)]
    simp [input,extra,show i.val ≠ 0 by omega]

end
end NearCubicWires.RepairSource.CloseoutSchedule.Cold
