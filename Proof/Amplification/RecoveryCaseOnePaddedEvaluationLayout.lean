import Proof.Amplification.RecoveryCaseOneCropPrepare

/-! The padded evaluator physically computes its crop width from the actual
generated schema, crops the target address, then evaluates the same table. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOnePaddedEvaluation
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def prepareSlots (i : Fin 18) : Fin 46 := i.castAdd 28
def cropSlots : Fin 4→Fin 46 := ![17,18,15,19]
def evalSlots (i : Fin 28) : Fin 46 :=
  if i.val=0 then 0 else if i.val=1 then 18 else ⟨18+i.val,by have hi:=i.isLt; omega⟩
theorem prepare_injective : Function.Injective prepareSlots := by
  intro i j h; exact Fin.ext (congrArg (fun z : Fin 46=>z.val) h)
theorem crop_injective : Function.Injective cropSlots := by decide
theorem eval_injective : Function.Injective evalSlots := by
  intro i j h
  have hv:=congrArg (fun z : Fin 46=>z.val) h
  apply Fin.ext
  dsimp only [evalSlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

def first := RecoveryFocus.machine prepareSlots RecoveryCaseOneCropPrepare.machine
def middle := RecoveryFocus.machine cropSlots RecoveryFieldCopy.machine
def last := RecoveryFocus.machine evalSlots RecoveryCaseOneEvaluation.machine
def machine := Composition.machine (Composition.machine first middle) last
def input (schema address : List Bool) (i : Fin 46) :=
  if i.val=0 then frame schema else if i.val=17 then frame address else []
def low {n target : Nat} (hn : n≤target) (address : BitInput target) : BitInput n :=
  fun i=>address (i.castLE hn)

theorem low_word {n target : Nat} (hn : n≤target) (address : BitInput target) :
    List.ofFn (low hn address)=(List.ofFn address).take n := by
  apply List.ext_getElem
  · simp [List.length_take,Nat.min_eq_left hn]
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_take,low]
    rfl

theorem padded_value {n target : Nat} (f : BoolFunction n) (hn : n≤target) (address : BitInput target) :
    RecoveryPipeline.padCore f hn address=f (low hn address) := by
  simp only [RecoveryPipeline.padCore,RecoveryPipeline.finSplitEquiv,Equiv.trans_apply]
  rfl

def budget {n target : Nat} (f : BoolFunction n) (hn : n≤target) (address : BitInput target) :=
  (RecoveryCaseOneCropPrepare.budget n (boolFunctionTable f)+1+(8*n+10))+1+
    RecoveryCaseOneEvaluation.budget f (low hn address)

end
end NearCubicWires.RepairSource.RecoveryCaseOnePaddedEvaluation
