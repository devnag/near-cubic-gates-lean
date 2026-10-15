import Proof.CaseAnalysis.CommonProgramRecoveryPorts

/-! The actual five Case2 inputs and its fresh result are wired to retained
recovery fields. In particular the bound is scalar2, not capacity scalar1. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose CloseoutLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

private theorem six_injective {n : ℕ} (f : Fin 6→Fin n) (W O N G : ℕ)
    (hW : 0<W) (hO : W<O) (hN : O<N) (hG : 1664≤G)
    (hf : ∀ i,(f i).val=(![W,N+(G+787),0,N+1659,N+1661,O] : Fin 6→ℕ) i) :
    Function.Injective f:=by
  intro i j he
  have hv:=((hf i).symm.trans ((congrArg Fin.val he).trans (hf j)))
  fin_cases i <;>fin_cases j <;>simp at hv ⊢ <;>omega

theorem two_shared_injective (p : Parameters) : Function.Injective (twoShared p):=by
  have hW : 0<(word0 p).val:=by
    have hq:0<(query0 p).val:=by
      change 0<(prefixProgram p).queryTape.val
      have h:=(prefixProgram p).queryFresh
      omega
    have hqw:=lt_trans (query_capacity p) (capacity_word p)
    omega
  have hO : (word0 p).val<(output0 p).val:=
    (CloseoutCommonPrefix.prepareSlots (work p) p.refuter p.k
      (CloseoutCommonPrepare.hierarchySlot p.k)).isLt
  have hN : (output0 p).val<n0 p:=(output0 p).isLt
  have hv : ∀ i,(twoShared p i).val=
      (![ (word0 p).val,(descriptionBank p).val,0,
        (scalarBank p 0).val,(scalarBank p 2).val,(output0 p).val] : Fin 6→ℕ) i:=by
    intro i
    fin_cases i <;>simp only [twoShared,Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.val_castAdd]
    rfl
  apply six_injective (twoShared p) (word0 p).val (output0 p).val (n0 p)
    (RecoveryBoundedCold.oldTapes (source p) p.k p.degree) hW hO hN (recovery_old_large p)
  intro i
  rw [hv,description_bank_value,scalar_bank_value,scalar_bank_value]
  rfl

theorem two_injective (p : Parameters) : Function.Injective (twoSlot p):=
  (Fin.castAdd_injective (n4 p) 2).comp
    (CloseoutCommonPortBank.injective _ _ (two_shared_injective p))

private theorem initial_five_injective {n : ℕ} (f : Fin 6→Fin n) (O : ℕ)
    (hO : 5≤O) (hf : ∀ i,(f i).val=(![0,1,2,3,4,O] : Fin 6→ℕ) i) :
    Function.Injective f:=by
  intro i j he
  have hv:=((hf i).symm.trans ((congrArg Fin.val he).trans (hf j)))
  fin_cases i <;>fin_cases j <;>simp at hv ⊢ <;>omega

theorem two_local_injective (p : Parameters) : Function.Injective (twoLocal p):=by
  apply initial_five_injective (twoLocal p)
    (140+CloseoutCaseTwo.Execution.foldTapes (source p) (selectedPCPP p.sources) p.k p.D p.copies)
    (by omega)
  intro i
  fin_cases i <;>rfl

theorem two_output (p : Parameters) :
    twoSlot p (CloseoutCaseTwo.DirectInput.outputPort
      (source p) (selectedPCPP p.sources) p.k p.D p.copies)=(ports p).outputTape:=by
  change (twoBank p (twoLocal p 5)).castAdd 2=_
  rw [twoBank,CloseoutCommonPortBank.shared_slot _ _ (two_local_injective p)]
  rfl

theorem two_inputs (p : Parameters) (j : Fin 6) :
    twoSlot p (twoLocal p j)=((twoShared p j).castAdd (tn p)).castAdd 2:=by
  change (twoBank p (twoLocal p j)).castAdd 2=_
  rw [twoBank,CloseoutCommonPortBank.shared_slot _ _ (two_local_injective p)]

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
