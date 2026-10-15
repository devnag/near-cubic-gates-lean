import Proof.MachineModel.BankCountLayout
import Proof.Hierarchy.HierarchyAllocation

/-! Exact field replacement by the count-conversion run: private scratch is
restored, and only count115 and the two native index words change. -/
namespace NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem output_same (C w M : ℕ) (j : Fin 18) (h0 : j≠0) (h11 : j≠11) (h15 : j≠15) :
    CountIndexClean.output C w M j=CountIndexCopy.input C w M j := by
  fin_cases j <;> simp_all [CountIndexClean.output,CountIndexCopy.input,CountIndexCopy.extra,
    CountIndex.padded,CountIndex.input,Fin.addCases,ZeroPadding.pad]

theorem replaced (A : Fin 128→List Bool) (C w M : ℕ)
    (ha : ∀ j,A (slots j)=CountIndexCopy.input C w M j) :
    install slots A (CountIndexClean.output C w M)=changed A C w M := by
  apply HierarchyAllocation.install_eq slots slots_injective
  · intro j
    by_cases h0 : j=0
    · subst j;simp only [changed,slots,CountIndexClean.output,Fin.isValue]
      rfl
    by_cases h11 : j=11
    · subst j;simp only [changed,slots,CountIndexClean.output,Fin.isValue]
      rfl
    by_cases h15 : j=15
    · subst j;simp only [changed,slots,CountIndexClean.output,Fin.isValue]
      rfl
    have n115 : slots j≠115:=by
      intro he
      exact h0 (slots_injective (show slots j=slots 0 from he))
    have n52 : slots j≠52:=by
      intro he
      exact h11 (slots_injective (show slots j=slots 11 from he))
    have n107 : slots j≠107:=by
      intro he
      exact h15 (slots_injective (show slots j=slots 15 from he))
    simp only [changed,Function.update_of_ne n107,Function.update_of_ne n52,Function.update_of_ne n115]
    exact (ha j).trans (output_same C w M j h0 h11 h15).symm
  · intro i hi
    have n115 : i≠115:=Ne.symm (hi 0)
    have n52 : i≠52:=Ne.symm (hi 11)
    have n107 : i≠107:=Ne.symm (hi 15)
    simp only [changed,Function.update_of_ne n107,Function.update_of_ne n52,Function.update_of_ne n115]

end NearCubicWires.ExtIncidence.BankCount
