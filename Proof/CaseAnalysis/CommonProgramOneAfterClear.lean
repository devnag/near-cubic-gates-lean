import Proof.CaseAnalysis.CommonProgramOneFields
import Proof.CaseAnalysis.CommonProgramClearPorts

/-! Case1 consumes the words physically installed by the paid query clear.
The clear bank cannot touch Case1's fresh work, hierarchy word or output. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

private theorem above {t u : ℕ} (f : Fin t→Fin u) (hv : ∀ j,(f j).val=j.val)
    (i : Fin u) (hi : t ≤ i.val) : ∀ j,f j≠i:=by
  intro j he
  have hj:=j.isLt
  have hh:=(hv j).symm.trans (congrArg Fin.val he)
  omega

theorem clear_one_fresh (p : Parameters) (i : Fin (on p)) :
    ∀ j,clearSlot p j≠lift3 p (i.natAdd (n2 p)):=by
  have hv : ∀ z : Fin (n2 p),(lift2 p z).val=z.val:=by
    intro z
    simp only [lift2,Fin.val_castAdd]
  exact fun j=>above (lift2 p) hv _ (Nat.le_add_right (n2 p) i.val) (clearBank p j)

theorem one_inputs (p : Parameters) (j : Fin 4) :
    oneSlot p (oneLocal p j)=lift3 p ((oneShared p j).castAdd (on p)):=
  congrArg (lift3 p) (CloseoutCommonPortBank.shared_slot _ _ (one_local_injective p) j)

theorem one_after_clear_entry (p : Parameters) (word bits : List Bool) (capacity : ℕ)
    (A : Fin (tapes p)→List Bool) (out : Fin 28→List Bool)
    (hw : A (lift0 p (word0 p))=word) (ho : A (ports p).outputTape=[])
    (fresh : ∀ i : Fin (on p),A (lift3 p (i.natAdd (n2 p)))=[])
    (ha : out 0=frame bits) (hq : out 26=List.replicate capacity false) :
    ∀ i,install (clearSlot p) A out (oneSlot p i)=oneInput p word bits capacity i:=by
  let B:=install (clearSlot p) A out
  have fields : ∀ j,B (oneSlot p (oneLocal p j))=
      oneInput p word bits capacity (oneLocal p j):=by
    intro j
    fin_cases j
    · exact ((congrArg B (one_word p)).trans
        ((install_other _ _ _ _ (clear_header_outside p 3 (by decide) (by decide))).trans hw)).trans
        (one_input_fields p word bits capacity 0).symm
    · exact ((congrArg B ((one_address p).trans (clear_address p).symm)).trans
        ((install_slot _ (clear_injective p) _ _ 0).trans ha)).trans
        (one_input_fields p word bits capacity 1).symm
    · exact ((congrArg B ((one_query p).trans (clear_query p).symm)).trans
        ((install_slot _ (clear_injective p) _ _ 26).trans hq)).trans
        (one_input_fields p word bits capacity 2).symm
    · exact ((congrArg B (one_output p)).trans
        ((install_other _ _ _ _ (clear_header_outside p 4 (by decide) (by decide))).trans ho)).trans
        (one_input_fields p word bits capacity 3).symm
  apply one_entry p word bits capacity B
  · intro j
    exact (congrArg B (one_inputs p j).symm).trans (fields j)
  · intro i
    exact (install_other _ _ _ _ (clear_one_fresh p i)).trans (fresh i)

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
