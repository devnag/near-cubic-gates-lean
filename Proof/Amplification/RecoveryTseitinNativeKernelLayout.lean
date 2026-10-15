import Proof.Amplification.RecoveryTseitinNativeReferenceDriver

/-! Route actual native references and their generated driver to the exact
node-clause kernel, with a separate reusable arithmetic and output bank. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def kernelFront (inputNode : Bool) : Fin 5→Fin 1335 := ![10,if inputNode then 11 else 12,13,17,18]
def kernelSlots (inputNode : Bool) : Fin 241→Fin 1335 :=
  Fin.addCases (m:=5) (n:=236) (motive:=fun _=>Fin 1335) (kernelFront inputNode)
    (fun j=>⟨1099+j.val,by have hj:=j.isLt; omega⟩)
theorem kernel_injective (inputNode : Bool) : Function.Injective (kernelSlots inputNode) := by
  intro i j
  refine Fin.addCases (m:=5) (n:=236) (fun a=>?_) (fun a=>?_) i
  · refine Fin.addCases (m:=5) (n:=236) (fun b=>?_) (fun b=>?_) j
    · intro he
      simp only [kernelSlots,Fin.addCases_left] at he
      have h : a=b := (show Function.Injective (kernelFront inputNode) by cases inputNode <;> decide) he
      exact congrArg (Fin.castAdd 236) h
    · intro he
      have h:=congrArg Fin.val he
      simp only [kernelSlots,Fin.addCases_left,Fin.addCases_right] at h
      cases inputNode <;> fin_cases a <;> dsimp [kernelFront] at h <;> omega
  · refine Fin.addCases (m:=5) (n:=236) (fun b=>?_) (fun b=>?_) j
    · intro he
      have h:=congrArg Fin.val he
      simp only [kernelSlots,Fin.addCases_left,Fin.addCases_right] at h
      cases inputNode <;> fin_cases b <;> dsimp [kernelFront] at h <;> omega
    · intro he
      have h:=congrArg Fin.val he
      simp only [kernelSlots,Fin.addCases_right] at h
      apply Fin.ext
      change 1099+a.val=1099+b.val at h
      change 5+a.val=5+b.val
      omega

def kernelWork (i : Fin 235) : Fin 1335 :=
  if i.val<234 then ⟨1099+i.val,by omega⟩ else 1334
def kernelBankSlots : Fin 237→Fin 1335 :=
  Fin.addCases (m:=236) (n:=1) (motive:=fun _=>Fin 1335)
    (Fin.addCases (m:=235) (n:=1) (motive:=fun _=>Fin 1335) kernelWork (fun _=>17)) (fun _=>18)
theorem bank_slots_value (i : Fin 237) : (kernelBankSlots i).val=
    if i.val<234 then 1099+i.val else if i.val=234 then 1334 else if i.val=235 then 17 else 18 := by
  refine Fin.addCases (m:=236) (n:=1) (fun a=>?_) (fun a=>?_) i
  · refine Fin.addCases (m:=235) (n:=1) (fun b=>?_) (fun b=>?_) a
    · simp only [kernelBankSlots,Fin.addCases_left,Fin.val_castAdd,kernelWork]
      split_ifs <;> dsimp <;> omega
    · fin_cases b; rfl
  · fin_cases a; rfl
theorem kernel_bank_injective : Function.Injective kernelBankSlots := by
  intro i j he
  have h:=congrArg Fin.val he
  rw [bank_slots_value,bank_slots_value] at h
  have hi:=i.isLt
  have hj:=j.isLt
  apply Fin.ext
  split_ifs at h <;> omega

end NearCubicWires.RepairSource.RecoveryTseitinNative
