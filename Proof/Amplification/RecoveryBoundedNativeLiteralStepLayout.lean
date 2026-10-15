import Proof.Amplification.RecoveryBoundedNativeLiteralStackRun
import Proof.Amplification.RecoveryTseitinRawIncrement

/-! The literal-loop body uses the already retained printing capacity and
reset log. Its address cell is padded for real scratch erasure and reuse. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeLiteralStep
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def advanceSlots : Fin 3→Fin 34:=![30,25,33]
def incrementSlots : Fin 2→Fin 34:=![1,32]
def eraseSlots : Fin 3→Fin 34:=![30,22,23]
def padding (C : ℕ) (i : Fin 34) := if i=30 then C else 0
abbrev heads := RecoveryBoundedNativeLiteralStack.heads
def data (index position C : ℕ) (negative : Bool) (out stack : List Bool) (ref : ℕ) (i : Fin 34) : List Bool :=
  if i=30 then ZeroPadding.pad C (List.replicate ref true)
  else RecoveryBoundedNativeLiteralStack.data index position C negative out stack ref i
noncomputable def first := RecoveryBoundedNativeLiteralStack.machine
noncomputable def advance := RecoveryFocus.machine advanceSlots PCPPNativeQueryAdvance.machine
noncomputable def increment := RecoveryFocus.machine incrementSlots RepairSource.RecoveryTseitinRawIncrement.machine
noncomputable def erase := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def machine := Composition.machine (Composition.machine (Composition.machine first advance) increment) erase
noncomputable def entry (index position C : ℕ) (negative : Bool) (out stack : List Bool) :=
  (⟨machine.start,heads out stack,data index position C negative out stack 0⟩ : Configuration 34 _)

theorem advance_input (index position C ref : ℕ) (negative : Bool) (out stack : List Bool) (j : Fin 3) :
    heads out stack (advanceSlots j)=0 ∧ data index position C negative out stack ref (advanceSlots j)=
      ![ZeroPadding.pad C (List.replicate ref true),List.replicate position true,List.replicate C false] j := by
  fin_cases j <;> exact ⟨rfl,rfl⟩
theorem advance_tapes (index position C ref : ℕ) (negative : Bool) (out stack : List Bool) :
    install advanceSlots (data index position C negative out stack ref)
      ![ZeroPadding.pad C (List.replicate (ref+1) true),List.replicate (ref+1) true,List.replicate C false]=
      data index (ref+1) C negative out stack (ref+1) := by
  apply HierarchyWidth.install_eq advanceSlots (by decide)
  · intro j; fin_cases j <;> rfl
  · intro i hi
    have h0:=hi 0
    have h1:=hi 1
    fin_cases i
    all_goals first | exact False.elim (h0 rfl) | exact False.elim (h1 rfl) |
      simp [data,Fin.addCases,RecoveryBoundedNativeLiteralStack.data,RecoveryBoundedNativeLiteral.data,
        PCPPNativeClauseBank.data,RecoveryBoundedNativeLiteral.values]

theorem increment_input (index position C ref : ℕ) (negative : Bool) (out stack : List Bool) (j : Fin 2) :
    heads out stack (incrementSlots j)=0 ∧ data index position C negative out stack ref (incrementSlots j)=
      ![List.replicate index true,List.replicate C false] j := by
  fin_cases j <;> exact ⟨rfl,rfl⟩
theorem increment_tapes (index position C ref : ℕ) (negative : Bool) (out stack : List Bool) :
    install incrementSlots (data index position C negative out stack ref)
      ![List.replicate (index+1) true,List.replicate C false]=
      data (index+1) position C negative out stack ref := by
  apply HierarchyWidth.install_eq incrementSlots (by decide)
  · intro j; fin_cases j <;> rfl
  · intro i hi
    have h:=hi 0
    fin_cases i
    all_goals first | exact False.elim (h rfl) |
      simp [data,Fin.addCases,RecoveryBoundedNativeLiteralStack.data,RecoveryBoundedNativeLiteral.data,
        PCPPNativeClauseBank.data,RecoveryBoundedNativeLiteral.values]

theorem erase_input (index position C ref : ℕ) (negative : Bool) (out stack : List Bool) (j : Fin 3) :
    heads out stack (eraseSlots j)=0 ∧ data index position C negative out stack ref (eraseSlots j)=
      ![ZeroPadding.pad C (List.replicate ref true),List.replicate C true,List.replicate (C+1) false] j := by
  fin_cases j <;> exact ⟨rfl,rfl⟩
theorem erase_tapes (index position C ref : ℕ) (negative : Bool) (out stack : List Bool) :
    install eraseSlots (data index position C negative out stack ref)
      ![List.replicate C false,List.replicate C true,List.replicate (C+1) false]=
      data index position C negative out stack 0 := by
  apply HierarchyWidth.install_eq eraseSlots (by decide)
  · intro j; fin_cases j <;> rfl
  · intro i hi
    have h:=hi 0
    fin_cases i
    all_goals first | exact False.elim (h rfl) |
      simp [data,Fin.addCases,RecoveryBoundedNativeLiteralStack.data,RecoveryBoundedNativeLiteral.data,
        PCPPNativeClauseBank.data,RecoveryBoundedNativeLiteral.values]

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeLiteralStep
