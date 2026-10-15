import Proof.PCP.PCPPairBounds

/-! Fixed ordinary arithmetic controller for one Nat.pair node. Entry has
the two original fields, their physically normalized copies and paid width;
all arithmetic scratch is blank. The enclosing encoder supplies these fields. -/
namespace NearCubicWires.RepairOrdinary.PCPPair
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (left right : List Bool) : Fin 30 → List Bool := fun i =>
  if i.val=0 then frame (binary (width left right) (RadixSemantics.value left))
  else if i.val=1 then frame (binary (width left right) (RadixSemantics.value right))
  else if i.val=2 then frame left else if i.val=3 then frame right
  else if i.val=4 then List.replicate (width left right) true else []

def initializeFlag : Machine 30 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some
    ⟨1,fun i => if i.val=6 then some false else none,fun _ => .stay⟩ else none

def compareSlots : Fin 4 → Fin 30 := ![1,0,6,5]
def multiplySlots (left : Bool) : Fin 14 → Fin 30 := fun j =>
  if j.val=0 then if left then 2 else 3
  else if j.val=8 then if left then 0 else 1
  else if j.val=9 then 4 else ⟨7+j.val,by omega⟩
def firstAddSlots : Fin 4 → Fin 30 := ![10,0,21,22]
def secondAddSlots : Fin 4 → Fin 30 := ![21,1,26,27]
def rightAddSlots : Fin 4 → Fin 30 := ![10,0,26,27]

theorem compare_injective : Function.Injective compareSlots := by decide
theorem multiply_injective (left : Bool) : Function.Injective (multiplySlots left) := by
  cases left <;> decide
theorem firstAdd_injective : Function.Injective firstAddSlots := by decide
theorem secondAdd_injective : Function.Injective secondAddSlots := by decide
theorem rightAdd_injective : Function.Injective rightAddSlots := by decide

noncomputable def compareProgram := RecoveryFocus.machine compareSlots RecoveryRootRound.compareMachine
noncomputable def multiplyProgram (left : Bool) := RecoveryFocus.machine (multiplySlots left) HierarchyMultiplyEntry.machine
noncomputable def firstAddProgram := RecoveryFocus.machine firstAddSlots BoundaryAdvance.machine
noncomputable def secondAddProgram := RecoveryFocus.machine secondAddSlots BoundaryAdvance.machine
noncomputable def rightAddProgram := RecoveryFocus.machine rightAddSlots BoundaryAdvance.machine
abbrev multiplyStates := 20+Fintype.card (RecoveryCalls.Control HierarchyMultiply.sizes)+2
def sizes : Fin 7 → ℕ := ![2,7,multiplyStates,7,7,multiplyStates,7]
noncomputable def programs : (j : Fin 7) → Machine 30 (sizes j)
  | 0 => initializeFlag
  | 1 => compareProgram
  | 2 => multiplyProgram true
  | 3 => firstAddProgram
  | 4 => secondAddProgram
  | 5 => multiplyProgram false
  | 6 => rightAddProgram
def next (j : Fin 7) (_ : Fin (sizes j)) (bits : Fin 30 → Bool) : Option (Fin 7) :=
  if j=0 then some 1 else if j=1 then if bits 6 then some 2 else some 5
  else if j=2 then some 3 else if j=3 then some 4 else if j=5 then some 6 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def budget (left right : List Bool) :=
  256*(width left right+1)*(left.length+right.length+1)+20*(width left right+1)

theorem initialized_run (left right : List Bool) :
    ReadyRun initializeFlag 1 (input left right)
      (fun i => if i.val=6 then [false] else input left right i) := by
  have hs : step initializeFlag (initialConfiguration initializeFlag (input left right))=some
      (⟨1,fun _ => 0,fun i => if i.val=6 then [false] else input left right i⟩ : Configuration 30 2) := by
    simp only [step,initializeFlag,initialConfiguration,Fin.val_zero,↓reduceIte,Option.map_some]
    congr 1
    apply configuration_ext
    · rfl
    · funext i
      rfl
    · funext i
      simp only [applyAction]
      by_cases hi : i.val=6
      · simp [hi,input,writeTapeBit]
      · simp [hi]
  obtain ⟨r,hr,hf,hn⟩ := (Timed.single (by rfl : initializeFlag.halted (0 : Fin 2)=false) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i; rw [hf],hn⟩

end NearCubicWires.RepairOrdinary.PCPPair
