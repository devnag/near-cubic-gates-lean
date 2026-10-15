import Proof.PCP.PCPPQueryCachedReaders
import Proof.PCP.PCPSerializerCapacityPower
import Proof.MachineModel.ClockUnarySum

/-! Physical cached-query capacity from the two actual native emitter counts.
The sum and fixed polynomial are evaluated once; both counts are retained. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryCapacity
open LocalBitMultitape RecoveryRootRound RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (D : ℕ) := DimensionPolynomial.tapes D+3
def sumSlots (D : ℕ) : Fin 4→Fin (tapes D) := fun i=>⟨i.val,by have h:=i.isLt; dsimp [tapes,DimensionPolynomial.tapes]; omega⟩
def powerSlots (D : ℕ) (i : Fin (DimensionPolynomial.tapes D)) : Fin (tapes D) :=
  ⟨if i.val=0 then 2 else i.val+3,by have h:=i.isLt; dsimp [tapes]; split_ifs <;> omega⟩
theorem sum_injective (D : ℕ) : Function.Injective (sumSlots D) := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun i : Fin (tapes D)=>i.val) h
theorem power_injective (D : ℕ) : Function.Injective (powerSlots D) := by
  intro a b h
  apply Fin.ext
  have hv:=congrArg Fin.val h
  dsimp [powerSlots] at hv
  split_ifs at hv <;> omega

def input (D size arity : ℕ) : Fin (tapes D)→List Bool := fun i=>
  if i.val=0 then List.replicate size true else if i.val=1 then List.replicate arity true else []
noncomputable def summed (D size arity : ℕ) := install (sumSlots D) (input D size arity)
  ![List.replicate size true,List.replicate arity true,List.replicate (size+arity) true,
    List.replicate (size+arity+2) false]
noncomputable def sumMachine (D : ℕ) := RecoveryFocus.machine (sumSlots D) ClockUnarySum.machine
noncomputable def powerMachine (D K : ℕ) := RecoveryFocus.machine (powerSlots D) (PCPSerializerCapacity.Power.machine D K)
noncomputable def machine (D K : ℕ) := Composition.machine (sumMachine D) (powerMachine D K)
def outputSlot (D : ℕ) := powerSlots D (PCPSerializerCapacity.Power.outputSlot D)
def budget (D K size arity : ℕ) := 2*(size+arity)+7+PCPSerializerCapacity.Power.budget D K (size+arity)

theorem sum_ready (D size arity : ℕ) :
    ClockJoin.ReadyRun (sumMachine D) (2*(size+arity)+6) (input D size arity) (summed D size arity) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := ClockUnarySum.sum_ready size arity
  have h : ClockJoin.ReadyRun ClockUnarySum.machine (2*(size+arity)+6)
      ![List.replicate size true,List.replicate arity true,[],[]]
      ![List.replicate size true,List.replicate arity true,List.replicate (size+arity) true,
        List.replicate (size+arity+2) false] := ⟨r,hr,ht,hh,hs⟩
  exact h.focus (sumSlots D) (sum_injective D) (input D size arity) (by intro i; fin_cases i <;> rfl)

theorem summed_power (D size arity : ℕ) (i : Fin (DimensionPolynomial.tapes D)) :
    summed D size arity (powerSlots D i)=DimensionPolynomial.input D (size+arity) i := by
  classical
  by_cases hi : i.val=0
  · have he : powerSlots D i=sumSlots D 2 := Fin.ext (by simp [powerSlots,hi,sumSlots])
    rw [summed,he,install_slot _ (sum_injective D)]
    simp [DimensionPolynomial.input,hi]
  · rw [summed,install_other _ _ _ _ (by
      intro j he
      have hv:=congrArg Fin.val he
      have hj:=j.isLt
      dsimp [sumSlots,powerSlots] at hv
      rw [if_neg hi] at hv
      omega)]
    simp [input,powerSlots,hi,DimensionPolynomial.input]

theorem capacity_run (D K size arity : ℕ) : ∃ out,
    ClockJoin.ReadyRun (machine D K) (budget D K size arity) (input D size arity) out ∧
      out (sumSlots D 0)=List.replicate size true ∧
      out (sumSlots D 1)=List.replicate arity true ∧
      out (outputSlot D)=List.replicate (K*(size+arity+1)^D) true := by
  classical
  obtain ⟨powerOut,hp,_,hv⟩ := PCPSerializerCapacity.Power.capacity_run D K (size+arity)
  have hpower := hp.focus (powerSlots D) (power_injective D) (summed D size arity) (summed_power D size arity)
  have joined := ClockJoin.join _ _ _ _ _ _ _ (sum_ready D size arity) hpower
  have hb : (2*(size+arity)+6)+1+PCPSerializerCapacity.Power.budget D K (size+arity)=budget D K size arity := by
    unfold budget
    omega
  rw [hb] at joined
  refine ⟨_,joined,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by
      intro i he
      have hi:=congrArg Fin.val he
      dsimp only [powerSlots,sumSlots] at hi
      split_ifs at hi <;> omega)]
    exact install_slot _ (sum_injective D) _ _ 0
  · rw [install_other _ _ _ _ (by
      intro i he
      have hi:=congrArg Fin.val he
      dsimp only [powerSlots,sumSlots] at hi
      split_ifs at hi <;> omega)]
    exact install_slot _ (sum_injective D) _ _ 1
  · rw [outputSlot,install_slot _ (power_injective D)]
    exact hv

end NearCubicWires.RepairOrdinary.PCPPQueryCapacity
