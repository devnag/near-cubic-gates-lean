import Proof.CaseAnalysis.CommonProgramPorts
import Proof.CaseAnalysis.CommonPortBankAt

/-! The paid prefix supplies the literal three-field cold recovery input.
Every other recovery tape is a fresh, empty physical word. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def prefixRecoveryFields (p : Parameters) : Fin 3→Fin (prefixProgram p).base.tapeCount:=
  ![CloseoutCommonPrefix.prepareSlots (work p) p.refuter p.k
      (CloseoutCommonPrepare.hierarchySlot p.k),
    CloseoutCommonPrefix.prepareSlots (work p) p.refuter p.k
      (CloseoutCommonPrepare.capacitySlot p.k),(prefixProgram p).queryTape]

theorem recovery_shared_prefix (p : Parameters) (j : Fin 3) :
    lift1 p ((recoveryShared p j).castAdd (rn p))=prefixSlot p (prefixRecoveryFields p j):=by
  fin_cases j <;>rfl

theorem recovery_fresh_empty (p : Parameters) (bits : List Bool)
    (out : Fin (prefixProgram p).base.tapeCount→List Bool) (i : Fin (rn p)) :
    install (prefixSlot p) (input p bits) out (lift1 p (i.natAdd (n0 p)))=[]:=by
  have hp:=(prefixProgram p).base.twoTapes
  have hn:(prefixProgram p).base.tapeCount<n0 p:=by unfold n0;omega
  have hi : (lift1 p (i.natAdd (n0 p))).val=n0 p+i.val:=rfl
  have away : ∀ j,prefixSlot p j≠lift1 p (i.natAdd (n0 p)):=by
    intro j he
    have hv:=congrArg (fun z : Fin (tapes p)=>z.val) he
    have hj:=j.isLt
    change j.val=n0 p+i.val at hv
    omega
  rw [install_other _ _ _ _ away]
  change (if (lift1 p (i.natAdd (n0 p))).val=0 then frame bits else [])=[]
  rw [if_neg (by rw [hi];omega)]

theorem recovery_input (p : Parameters) (bits word : List Bool) (W padding : ℕ)
    (out : Fin (prefixProgram p).base.tapeCount→List Bool)
    (fields : ∀ j,out (prefixRecoveryFields p j)=RecoveryBoundedCold.sharedWords word W padding j)
    (i : Fin (rn p)) :
    install (prefixSlot p) (input p bits) out (recoverySlot p i)=
      RecoveryBoundedCold.queryInput (source p) p.k p.degree word W padding i:=by
  apply CloseoutCommonPortBank.input_at
    (RecoveryBoundedCold.sharedLocal (source p) p.k p.degree) (recoveryShared p)
    (fun z=>install (prefixSlot p) (input p bits) out (lift1 p z))
    (RecoveryBoundedCold.queryInput (source p) p.k p.degree word W padding)
  · intro j
    exact (congrArg (install (prefixSlot p) (input p bits) out) (recovery_shared_prefix p j)).trans
      ((install_slot _ (prefix_injective p) _ _ _).trans ((fields j).trans
        (RecoveryBoundedCold.shared_input_port (source p) p.k p.degree word W padding j).symm))
  · exact recovery_fresh_empty p bits out
  · exact RecoveryBoundedCold.shared_input_empty (source p) p.k p.degree word W padding

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
