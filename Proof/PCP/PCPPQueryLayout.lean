import Proof.PCP.PCPPQueryClauseStart
import Proof.PCP.PCPPQueryCapacityBounds

/-! One capacity producer is routed directly into the shared clause/support
bank. The original cached source is outside every arithmetic focus. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryCold
open LocalBitMultitape RecoveryRootRound RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (D : ℕ) := 21+PCPPQueryCapacity.tapes D
def bankSlots (D : ℕ) (i : Fin 21) : Fin (tapes D) := i.castAdd (PCPPQueryCapacity.tapes D)
def capacitySlots (D : ℕ) (i : Fin (PCPPQueryCapacity.tapes D)) : Fin (tapes D) :=
  ⟨if i.val=1 then 19 else if i.val=6+2*D then 17 else i.val+21,
    by have hi:=i.isLt; dsimp [tapes,PCPPQueryCapacity.tapes,DimensionPolynomial.tapes] at *; split_ifs <;> omega⟩
theorem bank_injective (D : ℕ) : Function.Injective (bankSlots D) := by
  intro a b h
  exact Fin.ext (congrArg (fun j : Fin (tapes D)=>j.val) h)
theorem capacity_injective (D : ℕ) : Function.Injective (capacitySlots D) := by
  intro a b h
  apply Fin.ext
  have hv:=congrArg Fin.val h
  dsimp [capacitySlots] at hv
  split_ifs at hv <;> omega

def input (D : ℕ) (source : List Bool) (size arity : ℕ) : Fin (tapes D)→List Bool := fun j=>
  if j.val=0 then source else if j.val=21 then List.replicate size true
  else if j.val=19 then List.replicate arity true else []
noncomputable def capacityMachine (D K : ℕ) := RecoveryFocus.machine (capacitySlots D) (PCPPQueryCapacity.machine D K)
noncomputable def bankMachine (D : ℕ) := RecoveryFocus.machine (bankSlots D) PCPPQueryClauseBank.startMachine
noncomputable def machine (D K : ℕ) := Composition.machine (capacityMachine D K) (bankMachine D)
def budget (D K size arity : ℕ) := PCPPQueryCapacity.budget D K size arity+1+2*arity+2*(K*(size+arity+1)^D)+15

theorem capacity_output_val (D : ℕ) : (PCPPQueryCapacity.outputSlot D).val=6+2*D := by
  simp [PCPPQueryCapacity.outputSlot,PCPPQueryCapacity.powerSlots,PCPSerializerCapacity.Power.outputSlot,
    DimensionPolynomial.binarySlots]
  omega

theorem input_capacity (D : ℕ) (source : List Bool) (size arity : ℕ)
    (i : Fin (PCPPQueryCapacity.tapes D)) :
    input D source size arity (capacitySlots D i)=PCPPQueryCapacity.input D size arity i := by
  dsimp [input,capacitySlots,PCPPQueryCapacity.input]
  split_ifs <;> simp_all
  all_goals omega

theorem powered_bank (D K : ℕ) (source : List Bool) (size arity : ℕ)
    (out : Fin (PCPPQueryCapacity.tapes D)→List Bool)
    (ha : out (PCPPQueryCapacity.sumSlots D 1)=List.replicate arity true)
    (hc : out (PCPPQueryCapacity.outputSlot D)=List.replicate (K*(size+arity+1)^D) true)
    (j : Fin 21) :
    install (capacitySlots D) (input D source size arity) out (bankSlots D j)=
      PCPPQueryClauseBank.input source arity (K*(size+arity+1)^D) j := by
  classical
  by_cases h17 : j.val=17
  · have he : bankSlots D j=capacitySlots D (PCPPQueryCapacity.outputSlot D) := by
      apply Fin.ext
      simp [bankSlots,capacitySlots,capacity_output_val,h17]
      omega
    rw [he,install_slot _ (capacity_injective D),hc]
    have hj : j=17 := Fin.ext h17
    subst j
    rfl
  by_cases h19 : j.val=19
  · have he : bankSlots D j=capacitySlots D (PCPPQueryCapacity.sumSlots D 1) := by
      apply Fin.ext
      simp [bankSlots,capacitySlots,PCPPQueryCapacity.sumSlots,h19]
    rw [he,install_slot _ (capacity_injective D),ha]
    have hj : j=19 := Fin.ext h19
    subst j
    rfl
  · rw [install_other _ _ _ _ (by
      intro i he
      have hv:=congrArg Fin.val he
      have hj:=j.isLt
      dsimp [capacitySlots,bankSlots] at hv
      split_ifs at hv <;> omega)]
    have hn17 : j≠17 := by intro he; subst j; contradiction
    have hn19 : j≠19 := by intro he; subst j; contradiction
    simp [input,bankSlots,PCPPQueryClauseBank.input,hn17,hn19,h19,show j.val≠21 by have h:=j.isLt; omega]

end NearCubicWires.RepairOrdinary.PCPPQueryCold
