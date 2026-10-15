import Proof.Amplification.RecoveryBoundedNativeReference

/-! Fixed docking of actual literal bytes, its computed raw output address,
and the reverse unary stack needed by the original conjunction schedule. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeLiteralStack
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sumSlots : Fin 4→Fin 34 := ![25,29,30,32]
def pushSlots : Fin 3→Fin 34 := ![30,31,33]
def heads (out stack : List Bool) : Fin 34→ℕ :=
  Fin.addCases (m:=30) (n:=4) (motive:=fun _=>ℕ) (RecoveryBoundedNativeLiteral.heads out) ![0,stack.length,0,0]
def data (index position C : ℕ) (negative : Bool) (out stack : List Bool) (ref : ℕ) : Fin 34→List Bool :=
  Fin.addCases (m:=30) (n:=4) (motive:=fun _=>List Bool) (RecoveryBoundedNativeLiteral.data index position C negative out)
    ![List.replicate ref true,stack,List.replicate C false,List.replicate C false]
noncomputable def first := TapeEmbedding.machine 4 RecoveryBoundedNativeLiteral.machine
noncomputable def second := RecoveryFocus.machine sumSlots ClockUnarySum.machine
noncomputable def last := RecoveryFocus.machine pushSlots PCPUnaryStackPush.machine
noncomputable def machine := Composition.machine (Composition.machine first second) last
noncomputable def entry (index position C : ℕ) (negative : Bool) (out stack : List Bool) :=
  (⟨machine.start,heads out stack,data index position C negative out stack 0⟩ : Configuration 34 _)
def stackWord (ref : ℕ) (stack : List Bool) := stack++(frame (List.replicate ref true)).reverse

theorem sum_input (index position C : ℕ) (negative : Bool) (out stack : List Bool) (j : Fin 4) :
    heads out stack (sumSlots j)=0 ∧
    data index position C negative out stack 0 (sumSlots j)=
      ![List.replicate position true,[negative],[],List.replicate C false] j := by
  fin_cases j <;> exact ⟨rfl,rfl⟩

theorem sum_tapes (index position C : ℕ) (negative : Bool) (out stack : List Bool) :
    install sumSlots (data index position C negative out stack 0)
      ![List.replicate position true,[negative],List.replicate (position+negative.toNat) true,List.replicate C false]=
      data index position C negative out stack (position+negative.toNat) := by
  apply HierarchyWidth.install_eq sumSlots (by decide)
  · intro j; fin_cases j <;> rfl
  · intro i hi
    have h:=hi 2
    fin_cases i
    all_goals first | exact False.elim (h rfl) | rfl

theorem push_input (index position C ref : ℕ) (negative : Bool) (out stack : List Bool) (j : Fin 3) :
    heads out stack (pushSlots j)=![0,stack.length,0] j ∧
    data index position C negative out stack ref (pushSlots j)=
      ![List.replicate ref true,stack,List.replicate C false] j := by
  fin_cases j <;> exact ⟨rfl,rfl⟩

theorem push_tapes (index position C ref : ℕ) (negative : Bool) (out stack : List Bool) :
    install pushSlots (data index position C negative out stack ref)
      ![List.replicate ref true,stackWord ref stack,List.replicate C false]=
      data index position C negative out (stackWord ref stack) ref := by
  apply HierarchyWidth.install_eq pushSlots (by decide)
  · intro j; fin_cases j <;> rfl
  · intro i hi
    have h:=hi 1
    fin_cases i
    all_goals first | exact False.elim (h rfl) | rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeLiteralStack
