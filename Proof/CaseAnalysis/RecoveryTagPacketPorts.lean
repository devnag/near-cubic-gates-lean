import Proof.CaseAnalysis.RecoveryTagReferencePadded

/-! Only the existing counter, saved constant, scratch and one C-backed
packet are needed to print all five original tag-reference fields. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTagPacket
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (out : List Bool) : Fin 8→ℕ:=![0,0,0,0,0,0,0,out.length]
def data (current constant C : ℕ) (out : List Bool) : Fin 8→List Bool:=
  ![List.replicate current true,ZeroPadding.pad C (List.replicate constant true),
    List.replicate C false,List.replicate C false,List.replicate C false,
    List.replicate C true,List.replicate (C+1) false,ZeroPadding.pad C out]
def referenceSlots (useConstant : Bool) : Fin 7→Fin 8:=![if useConstant then 1 else 0,2,3,4,7,5,6]
theorem reference_injective (useConstant : Bool) : Function.Injective (referenceSlots useConstant) := by
  cases useConstant <;> decide
noncomputable def reference (useConstant : Bool):=RecoveryFocus.machine (referenceSlots useConstant) RecoveryBoundedTagReferenceAppend.machine
def selectedValue (useConstant : Bool) (current constant : ℕ):=if useConstant then constant else current
def sourceCap (useConstant : Bool) (C : ℕ):=if useConstant then C else 0

theorem reference_heads (useConstant : Bool) (out : List Bool) (j : Fin 7) :
    heads out (referenceSlots useConstant j)=RecoveryBoundedTagReferenceAppend.heads out j := by
  cases useConstant <;> fin_cases j <;> rfl

theorem reference_tapes (useConstant : Bool) (current constant C : ℕ) (out : List Bool) (j : Fin 7) :
    data current constant C out (referenceSlots useConstant j)=
      RecoveryBoundedTagReferenceAppend.paddedData (selectedValue useConstant current constant) (sourceCap useConstant C) C out j := by
  cases useConstant <;> fin_cases j <;> first
  | rfl
  | exact (ZeroPadding.pad_zero _).symm

def fixedData (current constant C : ℕ):=data current constant C []
theorem data_override (current constant C : ℕ) (out : List Bool) :
    data current constant C out=fun i=>if i=7 then ZeroPadding.pad C out else fixedData current constant C i := by
  funext i
  fin_cases i <;> rfl

theorem reference_install (useConstant : Bool) (current constant C : ℕ) (out result : List Bool) :
    install (referenceSlots useConstant) (data current constant C out)
      (RecoveryBoundedTagReferenceAppend.paddedData (selectedValue useConstant current constant) (sourceCap useConstant C) C result)=
      data current constant C result := by
  apply HierarchyWidth.install_eq (referenceSlots useConstant) (reference_injective useConstant)
  · exact reference_tapes useConstant current constant C result
  · intro i hi
    have h7 : i≠7:=fun h=>hi 4 h.symm
    simp only [data_override,if_neg h7]

def incrementSlots : Fin 2→Fin 8:=![0,4]
noncomputable def increment:=RecoveryFocus.machine incrementSlots RepairSource.RecoveryTseitinRawIncrement.machine

end NearCubicWires.RepairOrdinary.RecoveryBoundedTagPacket
