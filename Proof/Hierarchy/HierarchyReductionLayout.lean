import Proof.Hierarchy.HierarchyFromInput
import Proof.Hierarchy.HierarchyAllocation
import Proof.Hierarchy.HierarchyHeader
import Proof.Hierarchy.HierarchyPaddingLayout

/-! Literal layout of the complete hierarchy padding reduction. C remains
the hierarchy clock coefficient; the independent Cpad controls the linear
allocation and never changes the simulated clock field. -/
namespace NearCubicWires.RepairOrdinary.HierarchyReduction
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def base (k : ℕ) := HierarchyFromInput.tapes (k+2)
def tapes (k : ℕ) := base k+15
def low (k : ℕ) (i : Fin (base k)) : Fin (tapes k) := Fin.castAdd 15 i
def extra (k : ℕ) (i : Fin 15) : Fin (tapes k) := ⟨base k+i.val,by dsimp [tapes]; omega⟩
def xTape (k : ℕ) := low k (HierarchyFromInput.field (k+2) 2)
def boundTape (k : ℕ) := low k (HierarchyFromInput.outputTape (k+2) (by omega))
theorem base_lower (k : ℕ) : 35≤base k := HierarchyFromInput.tapes_lower (k+2)
theorem bound_bounds (k : ℕ) : 3≤(boundTape k).val ∧ (boundTape k).val<base k := by
  constructor
  · simp [boundTape,low,HierarchyFromInput.outputTape,HierarchyFromInput.boundSlots,
      HierarchyBound.outputTape,HierarchyBound.multiplySlots,HierarchyBound.extra,HierarchyPower.tapes]
  · exact (HierarchyFromInput.outputTape (k+2) (by omega)).isLt

def allocationSlots (k : ℕ) : Fin 10 → Fin (tapes k) := fun i =>
  if h : i.val=0 then xTape k else extra k ⟨i.val-1,by omega⟩
def sliceSlots (k : ℕ) : Fin 3 → Fin (tapes k) := ![extra k 7,extra k 9,extra k 10]
def codeSlots (k : ℕ) : Fin 2 → Fin (tapes k) := ![extra k 11,extra k 12]
def headerSlots (k : ℕ) : Fin 6 → Fin (tapes k) :=
  ![extra k 11,xTape k,boundTape k,extra k 9,extra k 13,extra k 14]
theorem low_injective (k : ℕ) : Function.Injective (low k) := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun i : Fin (tapes k) => i.val) h
theorem allocation_injective (k : ℕ) : Function.Injective (allocationSlots k) := by
  intro a b h
  apply Fin.ext
  have hl := base_lower k
  have he := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> simp [allocationSlots,extra,xTape,low,HierarchyFromInput.field] at he ⊢ <;> omega
theorem slice_injective (k : ℕ) : Function.Injective (sliceSlots k) := by
  intro a b h
  have he := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> simp [sliceSlots,extra] at he ⊢
theorem code_injective (k : ℕ) : Function.Injective (codeSlots k) := by
  intro a b h
  have he := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> simp [codeSlots,extra] at he ⊢
theorem header_injective (k : ℕ) : Function.Injective (headerSlots k) := by
  intro a b h
  have hl := base_lower k
  have hb := bound_bounds k
  have he := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> simp [headerSlots,extra,xTape,low,HierarchyFromInput.field] at he ⊢ <;> omega

def coefficient (Cpad : ℕ) := 2*Cpad+1
def constant (C Cpad : ℕ) (code : List Bool) := coefficient Cpad+HierarchyBinary.header code.length C
theorem allocation_value (C Cpad : ℕ) (code x : List Bool) :
    coefficient Cpad*x.length+constant C Cpad code=HierarchyBinary.allocation Cpad code.length C x.length := by
  dsimp [coefficient,constant,HierarchyBinary.allocation]
  ring
def input (k : ℕ) (x : List Bool) : Fin (tapes k) → List Bool := fun i =>
  if i.val=2 then frame x else []
def Fields (k C : ℕ) (x : List Bool) (ambient : Fin (tapes k) → List Bool) : Prop :=
  ambient (xTape k)=frame x ∧
  ambient (boundTape k)=frame (binary (HierarchyBinary.width C (k+2) x.length)
    (HierarchyBinary.bound C (k+2) x.length))
noncomputable def boundProgram (k C : ℕ) := RecoveryFocus.machine (low k)
  (HierarchyFromInput.machine (k+2) C (by omega))
noncomputable def allocationProgram (k C Cpad : ℕ) (code : List Bool) :=
  RecoveryFocus.machine (allocationSlots k) (HierarchyAllocation.machine (coefficient Cpad) (constant C Cpad code))
noncomputable def codeProgram (k : ℕ) (code : List Bool) :=
  RecoveryFocus.machine (codeSlots k) (HierarchyFixedWord.machine (frame code))
noncomputable def headerProgram (k : ℕ) := RecoveryFocus.machine (headerSlots k) HierarchyHeader.machine

end NearCubicWires.RepairOrdinary.HierarchyReduction
