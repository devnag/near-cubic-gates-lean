import Proof.Circuits.DecompositionInputDrivers
import Proof.Circuits.DecompositionCapacity

/-! Shared-source layout for the two checked cold producers. Degree and
coefficient stay abstract; all header work is a fresh additional bank. -/
namespace NearCubicWires.RepairOrdinary.DecompositionColdPrepare
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (D : ℕ) := PCPSerializerCapacity.tapes D+34
def old (D : ℕ) (i : Fin (PCPSerializerCapacity.tapes D)) : Fin (tapes D) := i.castAdd 34
def extra (j : Fin 35) : Fin 34 := ⟨j.val-1,by omega⟩
def headerSlot (D : ℕ) (j : Fin 35) : Fin (tapes D) :=
  if j.val=0 then old D (PCPSerializerCapacity.old D 0)
  else (extra j).natAdd (PCPSerializerCapacity.tapes D)
def capacitySlot (D : ℕ) := old D (PCPSerializerCapacity.capacitySlot D)

theorem headerSlot_injective (D : ℕ) : Function.Injective (headerSlot D) := by
  intro i j he
  have hv := congrArg Fin.val he
  have hT : 5 ≤ PCPSerializerCapacity.tapes D := by unfold PCPSerializerCapacity.tapes; omega
  dsimp only [headerSlot,old,PCPSerializerCapacity.old] at hv
  apply Fin.ext
  split_ifs at hv <;> simp only [Fin.val_castAdd,Fin.val_zero,Fin.val_natAdd,extra] at hv <;> omega

theorem headerSlot_ne_old (D : ℕ) (i : Fin (PCPSerializerCapacity.tapes D))
    (hi : i≠PCPSerializerCapacity.old D 0) (j : Fin 35) : headerSlot D j≠old D i := by
  intro he
  have hv := congrArg Fin.val he
  have hi0 : i.val≠0 := fun h => hi (Fin.ext h)
  have hit := i.isLt
  dsimp only [headerSlot,old,PCPSerializerCapacity.old] at hv
  split_ifs at hv <;> simp only [Fin.val_castAdd,Fin.val_zero,Fin.val_natAdd,extra] at hv <;> omega

theorem headerSlot_ne_capacity (D : ℕ) (j : Fin 35) : headerSlot D j≠capacitySlot D := by
  apply headerSlot_ne_old
  exact PCPSerializerCapacity.slots_ne_old D 0 (by decide) _

theorem header_input (a m : ℕ) (tail : List Bool) (j : Fin 35) :
    DecompositionInputDrivers.input a m tail j=
      if j.val=0 then frame (DecompositionInputCounts.word a m tail) else [] := by
  refine Fin.addCases (m:=23) (n:=12) (fun i => ?_) (fun i => ?_) j
  · simp only [DecompositionInputDrivers.input,Fin.addCases_left,DecompositionInputCounts.input,Fin.val_castAdd]
    rfl
  · have hi : 23+i.val≠0 := by omega
    simp only [DecompositionInputDrivers.input,Fin.addCases_right,Fin.val_natAdd,hi,ite_false]

noncomputable def first (D C : ℕ) := TapeEmbedding.machine 34 (DecompositionCapacity.machine D C)
noncomputable def header (D : ℕ) := RecoveryFocus.machine (headerSlot D) DecompositionInputDrivers.machine
noncomputable def machine (D C : ℕ) := Composition.machine (first D C) (header D)
def input (D : ℕ) (payload : List Bool) : Fin (tapes D) → List Bool :=
  Fin.addCases (DecompositionCapacity.input D (frame payload) []) (fun _ : Fin 34 => [])
def budget (D C a m : ℕ) (tail : List Bool) :=
  DecompositionCapacity.budget D C (frame (DecompositionInputCounts.word a m tail)).length+
    1+DecompositionInputDrivers.budget a m tail

end NearCubicWires.RepairOrdinary.DecompositionColdPrepare
