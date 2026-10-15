import Proof.Amplification.RecoveryTseitinReferenceReadOnly

/-! The actual cold-node controller never writes either retained raw counter. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryTseitinReadOnly
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem operands_readonly (i : Fin 2) : NoWrite operandsMachine (i.castAdd 1097) := by
  apply composition
  · apply composition
    · exact unselected readSlots _ _ (read_other _ (Or.inl (by change i.val < 1062; omega)))
    · apply unselected (argSlots false)
      fin_cases i <;> decide
  · apply unselected (argSlots true)
    fin_cases i <;> decide
theorem references_readonly (i : Fin 2) : NoWrite referencesMachine (i.castAdd 1097) :=
  composition _ _ _ (operands_readonly i)
    (focus referenceSlots reference_injective RecoveryTseitinReferences.coldMachine (i.castAdd 1060)
      (RecoveryTseitinReferences.cold_readonly i))
theorem prepare_readonly (i : Fin 2) : NoWrite prepareMachine (i.castAdd 1333) :=
  embedded 236 referencesMachine (i.castAdd 1097) (references_readonly i)
theorem kernel_counter_away (flag : Bool) (i : Fin 2) : ∀ j,kernelSlots flag j≠i.castAdd 1333 := by
  intro j
  refine Fin.addCases (m:=5) (n:=236) (fun k=>?_) (fun k=>?_) j
  · intro he
    have hv:=congrArg Fin.val he
    simp only [kernelSlots,Fin.addCases_left] at hv
    have hi:=i.isLt
    cases flag <;> fin_cases k <;> dsimp [kernelFront] at hv <;> omega
  · intro he
    have hv:=congrArg Fin.val he
    simp only [kernelSlots,Fin.addCases_right] at hv
    change 1099+k.val=i.val at hv
    omega
theorem tag_readonly (value : Bool) (i : Fin 2) : NoWrite (NodeController.tagProgram value) (i.castAdd 1333) := by
  apply unselected (NodeController.tagSlots value)
  cases value <;> fin_cases i <;> decide
theorem controller_readonly (i : Fin 2) : NoWrite NodeController.machine (i.castAdd 1333) := by
  apply calls
  intro j
  fin_cases j
  · exact tag_readonly false i
  · exact tag_readonly true i
  all_goals exact unselected (kernelSlots _) _ _ (kernel_counter_away _ i)
theorem cold_node_readonly (i : Fin 2) : NoWrite coldNodeMachine (i.castAdd 1333) :=
  composition _ _ _ (composition _ _ _ (prepare_readonly i)
    (unselected kernelBankSlots _ _ (bank_away _ (Or.inl (by change i.val < 17; omega)))))
    (controller_readonly i)
theorem cold_node_counters {n : Nat} (index : Nat) (node : BooleanNode n)
    (pre tail out : List Bool) (r : ExecutionReceipt 1335 _) (fuel : Nat)
    (hr : runFrom coldNodeMachine fuel
      ⟨coldNodeMachine.start,coldHeads pre out,coldInput n index
        (PCPPNativeNodeRead.source pre tail (PCPPRequestNodeSchema.tag node).val
          (PCPPRequestNodeSchema.fields node 1) (PCPPRequestNodeSchema.fields node 2)) out⟩=some r) :
    r.final.tapes 0=List.replicate n true ∧ r.final.tapes 1=List.replicate index true :=
  ⟨run_tape coldNodeMachine 0 (cold_node_readonly 0) fuel _ r hr,
    run_tape coldNodeMachine 1 (cold_node_readonly 1) fuel _ r hr⟩

end NearCubicWires.RepairSource.RecoveryTseitinNative
