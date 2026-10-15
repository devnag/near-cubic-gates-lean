import Proof.CaseAnalysis.CommonProgramPorts

/-! The paid query clear shares exactly the retained final address and
the common query. The hierarchy request and Boolean result are untouched. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem clear_local_injective : Function.Injective clearLocal:=by decide
theorem clear_query (p : Parameters) : clearSlot p 26=(ports p).queryTape:=by
  change lift2 p (clearBank p (clearLocal 1))=_
  rw [clearBank,CloseoutCommonPortBank.shared_slot _ _ clear_local_injective]
  rfl
theorem clear_address (p : Parameters) : clearSlot p 0=lift0 p (address0 p):=by
  change lift2 p (clearBank p (clearLocal 0))=_
  rw [clearBank,CloseoutCommonPortBank.shared_slot _ _ clear_local_injective]
  rfl

theorem clear_outside (p : Parameters) (i : Fin (n1 p))
    (hi : ∀ j,clearShared p j≠i) (j : Fin 28) : clearSlot p j≠lift1 p i:=by
  intro he
  have hbank : clearBank p j=i.castAdd 28:=lift2_injective p he
  exact CloseoutCommonPortBank.outside _ _ i hi j hbank

theorem clear_header_outside (p : Parameters) (j : Fin 5) (h0 : j≠0) (h1 : j≠1) :
    ∀ i,clearSlot p i≠lift0 p (header p j):=by
  apply clear_outside
  intro i he
  have hn : (![0,1] : Fin 2→Fin 5) i=j:=by
    apply header_injective p
    apply Fin.castAdd_injective (n0 p) (rn p)
    fin_cases i
    · exact he
    · exact he
  fin_cases i
  · exact h0 hn.symm
  · exact h1 hn.symm

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
