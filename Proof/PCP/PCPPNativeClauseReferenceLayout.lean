import Proof.PCP.PCPPNativeClauseLiteralReady
import Proof.PCP.PCPPNativeClauseOffsetSelect
import Proof.MachineModel.OrdinaryWilliamsUnaryProduct
import Proof.Hierarchy.HierarchyWidth

/-! Actual literal-reference arithmetic: original code split, sign-selected
offset, multiplication by the physically supplied stride template, and sum. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseReference
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def splitSlots : Fin 4→Fin 13 := ![0,1,2,3]
def selectSlots : Fin 5→Fin 13 := ![2,5,6,7,8]
def productSlots : Fin 4→Fin 13 := ![1,4,9,10]
def sumSlots : Fin 4→Fin 13 := ![9,7,11,12]
theorem split_injective : Function.Injective splitSlots := by decide
theorem select_injective : Function.Injective selectSlots := by decide
theorem product_injective : Function.Injective productSlots := by decide
theorem sum_injective : Function.Injective sumSlots := by decide
noncomputable def splitMachine := RecoveryFocus.machine splitSlots PCPPNativeLiteralSplit.machine
noncomputable def selectMachine := RecoveryFocus.machine selectSlots PCPPNativeClauseOffset.machine
noncomputable def productMachine := RecoveryFocus.machine productSlots ClockUnaryProduct.machine
noncomputable def sumMachine := RecoveryFocus.machine sumSlots ClockUnarySum.machine
noncomputable def machine := Composition.machine
  (Composition.machine (Composition.machine splitMachine selectMachine) productMachine) sumMachine

def offset (sign : Bool) (p n : ℕ) := PCPPNativeClauseOffset.value sign p n
def input (index : ℕ) (sign : Bool) (stride p n : ℕ) (i : Fin 13) : List Bool :=
  if i=0 then UnaryTemplate.tape (2*index+sign.toNat) else if i=4 then UnaryTemplate.tape stride
  else if i=5 then List.replicate p true else if i=6 then List.replicate n true else []
def splitData (index : ℕ) (sign : Bool) (stride p n : ℕ) (i : Fin 13) : List Bool :=
  if i=1 then List.replicate index true else if i=2 then [sign]
  else if i=3 then List.replicate (2*index+sign.toNat+2) false else input index sign stride p n i
def selectedData (index : ℕ) (sign : Bool) (stride p n : ℕ) (i : Fin 13) : List Bool :=
  if i=7 then List.replicate (offset sign p n) true else if i=8 then List.replicate (offset sign p n+2) false
  else splitData index sign stride p n i
def productData (index : ℕ) (sign : Bool) (stride p n : ℕ) (i : Fin 13) : List Bool :=
  if i=9 then List.replicate (index*stride) true else if i=10 then List.replicate (index*(2*stride+3)+2) false
  else selectedData index sign stride p n i
def output (index : ℕ) (sign : Bool) (stride p n : ℕ) (i : Fin 13) : List Bool :=
  if i=11 then List.replicate (index*stride+offset sign p n) true
  else if i=12 then List.replicate (index*stride+offset sign p n+2) false else productData index sign stride p n i

theorem split_ready (index : ℕ) (sign : Bool) (stride p n : ℕ) :
    ClockJoin.ReadyRun splitMachine (4*index+2*sign.toNat+6)
      (input index sign stride p n) (splitData index sign stride p n) := by
  obtain ⟨r,hr,ht,hh,hs⟩:=PCPPNativeLiteralSplit.ready_run index sign
  have base : ClockJoin.ReadyRun PCPPNativeLiteralSplit.machine _ _ _ := ⟨r,hr,ht,hh,hs.le⟩
  have hf:=base.focus splitSlots split_injective (input index sign stride p n)
    (by intro j; fin_cases j <;> rfl)
  have he:=HierarchyWidth.install_eq splitSlots split_injective (input index sign stride p n)
    (splitData index sign stride p n)
    ![UnaryTemplate.tape (2*index+sign.toNat),List.replicate index true,[sign],
      List.replicate (2*index+sign.toNat+2) false] (by intro j; fin_cases j <;> rfl) (by
      intro i hi
      have h1 : i≠1 := fun h=>hi 1 (by rw [h]; rfl)
      have h2 : i≠2 := fun h=>hi 2 (by rw [h]; rfl)
      have h3 : i≠3 := fun h=>hi 3 (by rw [h]; rfl)
      simp [splitData,h1,h2,h3])
  rw [he] at hf
  exact hf

theorem select_ready (index : ℕ) (sign : Bool) (stride p n : ℕ) :
    ClockJoin.ReadyRun selectMachine (2*offset sign p n+6)
      (splitData index sign stride p n) (selectedData index sign stride p n) := by
  obtain ⟨r,hr,ht,hh,hs⟩:=PCPPNativeClauseOffset.ready_run sign p n
  have base : ClockJoin.ReadyRun PCPPNativeClauseOffset.machine _ _ _ := ⟨r,hr,ht,hh,hs.le⟩
  have hf:=base.focus selectSlots select_injective (splitData index sign stride p n)
    (by intro j; fin_cases j <;> rfl)
  have he:=HierarchyWidth.install_eq selectSlots select_injective (splitData index sign stride p n)
    (selectedData index sign stride p n)
    ![[sign],List.replicate p true,List.replicate n true,List.replicate (offset sign p n) true,
      List.replicate (offset sign p n+2) false] (by intro j; fin_cases j <;> rfl) (by
      intro i hi
      have h7 : i≠7 := fun h=>hi 3 (by rw [h]; rfl)
      have h8 : i≠8 := fun h=>hi 4 (by rw [h]; rfl)
      simp [selectedData,h7,h8])
  dsimp only [offset] at he
  rw [he] at hf
  exact hf

end NearCubicWires.RepairOrdinary.PCPPNativeClauseReference
