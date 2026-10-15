import Proof.Amplification.RecoveryTseitinNativePrepared

/-! Exact view of the physically initialized original node-clause kernel. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RecoveryTseitinNode RecoveryTseitinKernel
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nodeWords {n : Nat} (index : Nat) (node : BooleanNode n) (j : Fin 3) :=
  RecoveryTseitinReferences.fields n index (PCPPRequestNodeSchema.fields node 1) (PCPPRequestNodeSchema.fields node 2)
    (referencePorts (kind node) j)
def nodePadding {n : Nat} (index : Nat) (node : BooleanNode n) (j : Fin 3) :=
  List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (nativeReferences index node j)-
    (RepairOrdinary.frame (nativeReferences index node j).bits).length) false
def readyData {n : Nat} (index : Nat) (node : BooleanNode n) (i : Fin 239) : List Bool :=
  if h : i.val<3 then nodeWords index node ⟨i.val,h⟩ else
  if i=3 then List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) true else
  if i=4 then List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (n+index)+1) false else
  List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) false

theorem ready_references {n : Nat} (index : Nat) (node : BooleanNode n) (j : Fin 3) :
    readyData index node (sourceSlot j)=RepairOrdinary.frame (nativeReferences index node j).bits++nodePadding index node j := by
  simp only [readyData,sourceSlot,dif_pos j.isLt]
  rw [nodeWords,native_reference_fields]
  rfl
theorem ready_bounded {n : Nat} (index : Nat) (node : BooleanNode n) :
    Bounded (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) (readyData index node) := by
  intro i hi
  have h3 : i≠3 := by intro he; have h:=congrArg Fin.val he; change i.val=3 at h; omega
  have h4 : i≠4 := by intro he; have h:=congrArg Fin.val he; change i.val=4 at h; omega
  simp only [readyData,dif_neg (by omega : ¬i.val<3),if_neg h3,if_neg h4,List.length_replicate,le_refl]

theorem kernel_reference (k : Fin 6) (j : Fin 3) :
    kernelSlots (decide (k=2)) ((sourceSlot j).castAdd 2)=generatedRef (referencePorts k j) := by
  have he : (sourceSlot j).castAdd 2=(⟨j.val,by omega⟩ : Fin 5).castAdd 236 := Fin.ext rfl
  rw [he,kernelSlots,Fin.addCases_left]
  by_cases hk : k=2 <;> fin_cases j <;>
    simp [kernelFront,generatedRef,referenceSlots,RecoveryTseitinReferences.referenceSlot,
      referencePorts,hk]

theorem bank_away (i : Fin 1335) (hi : i.val < 17 ∨ (19 ≤ i.val ∧ i.val < 1099) ∨ i=1333) :
    ∀ j,kernelBankSlots j≠i := by
  intro j he
  have h:=congrArg Fin.val he
  rw [bank_slots_value] at h
  have hj:=j.isLt
  rcases hi with hi|hi|hi
  · split_ifs at h <;> omega
  · split_ifs at h <;> omega
  · subst i
    split_ifs at h <;> omega

end NearCubicWires.RepairSource.RecoveryTseitinNative
