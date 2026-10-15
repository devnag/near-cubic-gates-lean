import Proof.Hierarchy.HierarchyBoundLayout

/-! Paid physical transitions from the initial short fields to n^D+1 and
then to C*(n^D+1), with each next call consuming the preceding tapes. -/
namespace NearCubicWires.RepairOrdinary.HierarchyBound
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem power_ready (D C n : ℕ) (hD : 0<D) :
    ∃ middle,ClockJoin.ReadyRun (powerProgram D hD) (HierarchyPower.fullBudget D C n)
      (input D C n) middle ∧ Fields D C n hD (n^D) middle ∧
      Fresh middle (HierarchyPower.tapes D) := by
  obtain ⟨r,hr,hf,hh,hs⟩ := HierarchyPower.full_run D C n hD
  have h := (show ClockJoin.ReadyRun (HierarchyPower.fullMachine D hD) _ _ r.final.tapes from
    ⟨r,hr,rfl,hh,hs⟩).focus (low D) (low_injective D) (input D C n)
    (by intro j; rfl)
  refine ⟨_,h,?_,?_⟩
  · constructor
    · exact (install_slot _ (low_injective D) _ _ (HierarchyPower.outputTape D hD)).trans hf.2.2
    · exact (install_slot _ (low_injective D) _ _ ⟨1,by dsimp [HierarchyPower.tapes]; omega⟩).trans hf.2.1
  · apply fresh_install _ _ _ (HierarchyPower.tapes D) (HierarchyPower.tapes D) (by omega)
    · intro i hi
      have hp : 7≤HierarchyPower.tapes D := by dsimp [HierarchyPower.tapes]; omega
      simp [input,show i.val≠0 by omega,show i.val≠1 by omega]
    · intro j
      exact j.isLt

theorem successor_ready (D C n : ℕ) (hD : 0<D) (ambient : Fin (tapes D) → List Bool)
    (hf : Fields D C n hD (n^D) ambient) (hblank : Fresh ambient (HierarchyPower.tapes D)) :
    ∃ middle,ClockJoin.ReadyRun (successorProgram D hD) (8*HierarchyBinary.width C D n+9)
      ambient middle ∧ Fields D C n hD (n^D+1) middle ∧
      Fresh middle (HierarchyPower.tapes D+4) := by
  have hlocal := HierarchySuccessor.successor_ready (HierarchyBinary.width C D n) (n^D)
    (HierarchyBinary.successor_fit C D n)
  have h := hlocal.focus (successorSlots D hD) (successor_injective D hD) ambient
    (by intro j; fin_cases j
        · exact hf.1
        · exact hf.2
        · exact hblank _ (by simp [successorSlots,extra])
        · exact hblank _ (by simp [successorSlots,extra])
        · exact hblank _ (by simp [successorSlots,extra])
        · exact hblank _ (by simp [successorSlots,extra]))
  refine ⟨_,h,?_,?_⟩
  · exact ⟨install_slot _ (successor_injective D hD) _ _ 0,
      install_slot _ (successor_injective D hD) _ _ 1⟩
  · apply fresh_install _ _ _ (HierarchyPower.tapes D) _ (by omega) hblank
    intro j
    have hp := power_bounds D hD
    have hsize : 7≤HierarchyPower.tapes D := by dsimp [HierarchyPower.tapes]; omega
    fin_cases j <;> simp [successorSlots,extra,widthTape]; omega

def coefficientCost (C : ℕ) := 2*(frame C.bits).length+2

theorem coefficient_ready (D C n : ℕ) (hD : 0<D) (ambient : Fin (tapes D) → List Bool)
    (hf : Fields D C n hD (n^D+1) ambient) (hblank : Fresh ambient (HierarchyPower.tapes D+4)) :
    ∃ middle,ClockJoin.ReadyRun (coefficientProgram D C) (coefficientCost C)
      ambient middle ∧ Fields D C n hD (n^D+1) middle ∧
      middle (extra D 4)=frame C.bits ∧ Fresh middle (HierarchyPower.tapes D+6) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := HierarchyFixedWord.word_ready (frame C.bits)
  have hlocal : ClockJoin.ReadyRun (HierarchyFixedWord.machine (frame C.bits)) _ _ _ :=
    ⟨r,hr,ht,hh,hs.le⟩
  have h := hlocal.focus (coefficientSlots D) (coefficient_injective D) ambient
    (by intro j; fin_cases j <;> exact hblank _ (by simp [coefficientSlots,extra]))
  have hslots (j : Fin 2) : HierarchyPower.tapes D+4 ≤ (coefficientSlots D j).val := by
    fin_cases j <;> simp [coefficientSlots,extra]
  have hp := power_bounds D hD
  have hsize : 7≤HierarchyPower.tapes D := by dsimp [HierarchyPower.tapes]; omega
  refine ⟨_,h,?_,install_slot _ (coefficient_injective D) _ _ 0,?_⟩
  · constructor
    · rw [keep_install _ _ _ _ hslots _ (by omega)]
      exact hf.1
    · rw [keep_install _ _ _ _ hslots _ (by change 1<HierarchyPower.tapes D+4; omega)]
      exact hf.2
  · apply fresh_install _ _ _ (HierarchyPower.tapes D+4) _ (by omega) hblank
    intro j
    fin_cases j <;> simp [coefficientSlots,extra]

def multiplyCost (D C n : ℕ) := 128*(HierarchyBinary.width C D n+1)*(C.bits.length+1)

theorem multiply_ready (D C n : ℕ) (hD : 0<D) (ambient : Fin (tapes D) → List Bool)
    (hf : Fields D C n hD (n^D+1) ambient) (hc : ambient (extra D 4)=frame C.bits)
    (hblank : Fresh ambient (HierarchyPower.tapes D+6)) :
    ∃ middle,ClockJoin.ReadyRun (multiplyProgram D hD) (multiplyCost D C n) ambient middle ∧
      middle (multiplySlots D hD 3)=frame (binary (HierarchyBinary.width C D n) (HierarchyBinary.bound C D n)) ∧
      middle (widthTape D)=List.replicate (HierarchyBinary.width C D n) true := by
  obtain ⟨r,hr,hout,_,_,hwidth,_,hh,hs⟩ := HierarchyMultiplyEntry.multiply_run
    (HierarchyBinary.width C D n) (n^D+1) C.bits (HierarchyBinary.coefficient_call_fit C D n)
  have hlocal : ClockJoin.ReadyRun HierarchyMultiplyEntry.machine _ _ r.final.tapes :=
    ⟨r,hr,rfl,hh,hs⟩
  have hi : ∀ j,ambient (multiplySlots D hD j)=
      HierarchyMultiplyEntry.input14 (HierarchyBinary.width C D n) (n^D+1) C.bits j := by
    intro j
    fin_cases j
    · exact hc
    · exact hblank _ (by simp [multiplySlots,extra])
    · exact hblank _ (by simp [multiplySlots,extra])
    · exact hblank _ (by simp [multiplySlots,extra])
    · exact hblank _ (by simp [multiplySlots,extra])
    · exact hblank _ (by simp [multiplySlots,extra])
    · exact hblank _ (by simp [multiplySlots,extra])
    · exact hblank _ (by simp [multiplySlots,extra])
    · exact hf.1
    · exact hf.2
    · exact hblank _ (by simp [multiplySlots,extra])
    · exact hblank _ (by simp [multiplySlots,extra])
    · exact hblank _ (by simp [multiplySlots,extra])
    · exact hblank _ (by simp [multiplySlots,extra])
  have h := hlocal.focus (multiplySlots D hD) (multiply_injective D hD) ambient hi
  refine ⟨_,h,?_,(install_slot _ (multiply_injective D hD) _ _ 9).trans hwidth⟩
  rw [install_slot _ (multiply_injective D hD),hout,RecoveryUnpair.bits_value]
  simp only [HierarchyBinary.bound,Nat.mul_comm]

end NearCubicWires.RepairOrdinary.HierarchyBound
