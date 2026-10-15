import Proof.Hierarchy.HierarchyBinarySuccessor
import Proof.Amplification.RecoveryUnpairCode

/-! Finite physical layout for the hierarchy clock B_H=C*(n^D+1).
The coefficient and degree are fixed program parameters. -/
namespace NearCubicWires.RepairOrdinary.HierarchyBound
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (D : ℕ) := HierarchyPower.tapes D+17
def low (D : ℕ) (i : Fin (HierarchyPower.tapes D)) : Fin (tapes D) := Fin.castAdd 17 i
def extra (D : ℕ) (i : Fin 17) : Fin (tapes D) := ⟨HierarchyPower.tapes D+i.val,by dsimp [tapes]; omega⟩
def widthTape (D : ℕ) : Fin (tapes D) := ⟨1,by dsimp [tapes,HierarchyPower.tapes]; omega⟩
def powerTape (D : ℕ) (hD : 0<D) := low D (HierarchyPower.outputTape D hD)
theorem power_bounds (D : ℕ) (hD : 0<D) :
    2≤(powerTape D hD).val ∧ (powerTape D hD).val<HierarchyPower.tapes D := by
  constructor
  · simp [powerTape,low,HierarchyPower.outputTape,HierarchyPower.block]
  · exact (HierarchyPower.outputTape D hD).isLt

def successorSlots (D : ℕ) (hD : 0<D) : Fin 6 → Fin (tapes D) :=
  ![powerTape D hD,widthTape D,extra D 0,extra D 1,extra D 2,extra D 3]
def coefficientSlots (D : ℕ) : Fin 2 → Fin (tapes D) := ![extra D 4,extra D 5]
def multiplySlots (D : ℕ) (hD : 0<D) : Fin 14 → Fin (tapes D) :=
  fun i => if h0 : i.val=0 then extra D 4
    else if h8 : i.val=8 then powerTape D hD
    else if h9 : i.val=9 then widthTape D
    else if hi : i.val<8 then extra D ⟨i.val+5,by omega⟩
    else extra D ⟨i.val+3,by omega⟩
theorem low_injective (D : ℕ) : Function.Injective (low D) := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun i : Fin (tapes D) => i.val) h
theorem successor_injective (D : ℕ) (hD : 0<D) : Function.Injective (successorSlots D hD) := by
  intro a b h
  have hp := power_bounds D hD
  have he := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> simp [successorSlots,extra,widthTape] at he ⊢ <;> omega
theorem coefficient_injective (D : ℕ) : Function.Injective (coefficientSlots D) := by
  intro a b h
  have he := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> simp [coefficientSlots,extra] at he ⊢
theorem multiply_injective (D : ℕ) (hD : 0<D) : Function.Injective (multiplySlots D hD) := by
  intro a b h
  have hp := power_bounds D hD
  have he := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> simp [multiplySlots,extra,widthTape] at he ⊢ <;> omega

def Fresh {t : ℕ} (ambient : Fin t → List Bool) (cut : ℕ) : Prop :=
  ∀ i,cut ≤ i.val → ambient i=[]
theorem fresh_install {t u : ℕ} (slot : Fin t → Fin u) (ambient : Fin u → List Bool)
    (out : Fin t → List Bool) (before after : ℕ) (hle : before≤after)
    (hin : Fresh ambient before) (hs : ∀ j,(slot j).val<after) :
    Fresh (install slot ambient out) after := by
  intro i hi
  rw [install_other _ _ _ _ (by intro j he; have hv := congrArg Fin.val he; have := hs j; omega)]
  exact hin i (by omega)
theorem keep_install {t u : ℕ} (slot : Fin t → Fin u) (ambient : Fin u → List Bool)
    (out : Fin t → List Bool) (cut : ℕ) (hs : ∀ j,cut ≤ (slot j).val)
    (i : Fin u) (hi : i.val<cut) : install slot ambient out i=ambient i := by
  apply install_other
  intro j he
  have hv := congrArg Fin.val he
  have := hs j
  omega

def input (D C n : ℕ) : Fin (tapes D) → List Bool := fun i =>
  if i.val=0 then frame (ClockBinary.word n)
  else if i.val=1 then List.replicate (HierarchyBinary.width C D n) true else []
def Fields (D C n : ℕ) (hD : 0<D) (a : ℕ) (ambient : Fin (tapes D) → List Bool) : Prop :=
  ambient (powerTape D hD)=frame (binary (HierarchyBinary.width C D n) a) ∧
  ambient (widthTape D)=List.replicate (HierarchyBinary.width C D n) true
noncomputable def powerProgram (D : ℕ) (hD : 0<D) :=
  RecoveryFocus.machine (low D) (HierarchyPower.fullMachine D hD)
noncomputable def successorProgram (D : ℕ) (hD : 0<D) :=
  RecoveryFocus.machine (successorSlots D hD) HierarchySuccessor.machine
noncomputable def coefficientProgram (D C : ℕ) :=
  RecoveryFocus.machine (coefficientSlots D) (HierarchyFixedWord.machine (frame C.bits))
noncomputable def multiplyProgram (D : ℕ) (hD : 0<D) :=
  RecoveryFocus.machine (multiplySlots D hD) HierarchyMultiplyEntry.machine

end NearCubicWires.RepairOrdinary.HierarchyBound
