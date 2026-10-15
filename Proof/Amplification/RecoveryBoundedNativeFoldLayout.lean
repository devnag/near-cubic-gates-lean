import Proof.Amplification.RecoveryBoundedNativeFoldPop

/-! Reuse the same literal bank for the original reverse AND/OR fold.
The popped reference and its temporary frame occupy already paid storage. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeFold
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def values (ref acc : ℕ) : Fin 7→ℕ:=![0,ref,0,acc,0,0,0]
def oldData (ref acc C : ℕ) (out : List Bool) (i : Fin 29) : List Bool :=
  if i=1 then ZeroPadding.pad C (List.replicate ref true)
  else PCPPNativeClauseBank.data (values ref acc) C out i
def data (ref acc C : ℕ) (flag : Bool) (out stack framed : List Bool) : Fin 34→List Bool :=
  Fin.addCases (m:=29) (n:=5) (motive:=fun _=>List Bool) (oldData ref acc C out)
    ![[flag],ZeroPadding.pad C framed,stack,List.replicate C false,List.replicate C false]
def heads (out : List Bool) (live : ℕ) : Fin 34→ℕ :=
  Fin.addCases (m:=29) (n:=5) (motive:=fun _=>ℕ) (PCPPNativeClauseBank.heads out) ![0,0,live,0,0]
def popSlots : Fin 5→Fin 34:=![31,30,32,1,33]
def incrementSlots : Fin 2→Fin 34:=![25,32]
def eraseSlots : Fin 4→Fin 34:=![1,30,22,23]
def tag (conjunction : Bool) := if conjunction then 3 else 4
noncomputable def first:=RecoveryFocus.machine popSlots PCPUnaryStackPop.machine
noncomputable def second (conjunction : Bool):=TapeEmbedding.machine 5
  (PCPPNativeClauseBank.nodeMachine (tag conjunction) 0 1 0 3)
noncomputable def third:=RecoveryFocus.machine incrementSlots RepairSource.RecoveryTseitinRawIncrement.machine
noncomputable def last:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 2)
noncomputable def machine (conjunction : Bool):=Composition.machine
  (Composition.machine (Composition.machine first (second conjunction)) third) last
def emitted (conjunction : Bool) (ref acc : ℕ) := natWord (tag conjunction)++natWord ref++natWord acc
noncomputable def entry (conjunction : Bool) (acc C live : ℕ) (flag : Bool) (out stack : List Bool) :=
  (⟨(machine conjunction).start,heads out live,data 0 acc C flag out stack []⟩ : Configuration 34 _)

theorem pop_input (ref acc C z : ℕ) (flag : Bool) (out pre : List Bool) (j : Fin 5) :
    heads out (pre.length+2*ref+1) (popSlots j)=![pre.length+2*ref+1,0,0,0,0] j ∧
    data 0 acc C flag out (pre++(frame (List.replicate ref true)).reverse++List.replicate z false) [] (popSlots j)=
      ![pre++(frame (List.replicate ref true)).reverse++List.replicate z false,
        List.replicate C false,List.replicate C false,List.replicate C false,List.replicate C false] j := by
  fin_cases j <;> exact ⟨rfl,rfl⟩

theorem pop_tapes (ref acc C z : ℕ) (flag : Bool) (out pre : List Bool) :
    install popSlots
      (data 0 acc C flag out (pre++(frame (List.replicate ref true)).reverse++List.replicate z false) [])
      ![pre++List.replicate (2*ref+1+z) false,ZeroPadding.pad C (frame (List.replicate ref true)),
        List.replicate C false,ZeroPadding.pad C (List.replicate ref true),List.replicate C false]=
      data ref acc C flag out (pre++List.replicate (2*ref+1+z) false) (frame (List.replicate ref true)) := by
  apply HierarchyWidth.install_eq popSlots (by decide)
  · intro j; fin_cases j <;> rfl
  · intro i hi
    have h0:=hi 0
    have h1:=hi 1
    have h3:=hi 3
    fin_cases i
    all_goals first | exact False.elim (h0 rfl) | exact False.elim (h1 rfl) | exact False.elim (h3 rfl) |
      simp [data,oldData,values,Fin.addCases,PCPPNativeClauseBank.data]

theorem increment_input (ref acc C live : ℕ) (flag : Bool) (out stack framed : List Bool) (j : Fin 2) :
    heads out live (incrementSlots j)=0 ∧
    data ref acc C flag out stack framed (incrementSlots j)=![List.replicate acc true,List.replicate C false] j := by
  fin_cases j <;> exact ⟨rfl,rfl⟩
theorem increment_tapes (ref acc C : ℕ) (flag : Bool) (out stack framed : List Bool) :
    install incrementSlots (data ref acc C flag out stack framed)
      ![List.replicate (acc+1) true,List.replicate C false]=data ref (acc+1) C flag out stack framed := by
  apply HierarchyWidth.install_eq incrementSlots (by decide)
  · intro j; fin_cases j <;> rfl
  · intro i hi
    have h:=hi 0
    fin_cases i
    all_goals first | exact False.elim (h rfl) |
      simp [data,oldData,values,Fin.addCases,PCPPNativeClauseBank.data]

theorem erase_input (ref acc C live : ℕ) (flag : Bool) (out stack framed : List Bool) (j : Fin 4) :
    heads out live (eraseSlots j)=0 ∧ data ref acc C flag out stack framed (eraseSlots j)=
      ![ZeroPadding.pad C (List.replicate ref true),ZeroPadding.pad C framed,
        List.replicate C true,List.replicate (C+1) false] j := by
  fin_cases j <;> exact ⟨rfl,rfl⟩
theorem erase_tapes (ref acc C : ℕ) (flag : Bool) (out stack framed : List Bool) :
    install eraseSlots (data ref acc C flag out stack framed)
      ![List.replicate C false,List.replicate C false,List.replicate C true,List.replicate (C+1) false]=
      data 0 acc C flag out stack [] := by
  apply HierarchyWidth.install_eq eraseSlots (by decide)
  · intro j; fin_cases j <;> rfl
  · intro i hi
    have h0:=hi 0
    have h1:=hi 1
    fin_cases i
    all_goals first | exact False.elim (h0 rfl) | exact False.elim (h1 rfl) |
      simp [data,oldData,values,Fin.addCases,PCPPNativeClauseBank.data]

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeFold
