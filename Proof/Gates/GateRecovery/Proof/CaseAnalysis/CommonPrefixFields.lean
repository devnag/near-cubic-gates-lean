import Proof.Gates.GateRecovery.Proof.CaseAnalysis.CommonPrefixLayout

namespace GR

/-! Exact input fields for the paid common preparation. The first ordinary
program retains the final address and refuter answer; all preparation work
ports are fresh, with no physical copy or uncharged allocation. -/
namespace NearCubicWires.RepairSource.CloseoutCommonPrefix
open LocalBitMultitape RepairOrdinary CloseoutSchedule CloseoutRetainedRefuter RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem prepare_input_lookup (k : ℕ) (bits result : List Bool)
    (j : Fin (CloseoutCommonPrepare.tapes k)) :
    CloseoutCommonPrepare.input k bits result j=
      if j.val=0 then frame bits else if j.val=1 then frame result else []:=by
  refine Fin.addCases (fun i=>?_) (fun i=>?_) j
  · simp only [CloseoutCommonPrepare.input,CloseoutHierarchyRequest.Shared.input,
      Fin.addCases_left,Fin.val_castAdd,CloseoutCommonPrepare.ambient]
    rfl
  · simp only [CloseoutCommonPrepare.input,CloseoutHierarchyRequest.Shared.input,
      Fin.addCases_right,Fin.val_natAdd]
    rw [if_neg (by omega),if_neg (by omega)]

theorem prepare_address (w : ℕ) (r : OrdinaryOracleProgram) (k : ℕ) :
    prepareSlots w r k (CloseoutCommonPrepare.addressSlot k)=firstSlots w r k (address w r):=by
  rw [first_address]
  rfl

theorem prepare_answer (w : ℕ) (r : OrdinaryOracleProgram) (k : ℕ) :
    prepareSlots w r k (CloseoutCommonPrepare.answerSlot k)=firstSlots w r k (answer w r):=by
  rfl

theorem work_ne_first (w : ℕ) (r : OrdinaryOracleProgram) (k : ℕ)
    (j : Fin (CloseoutCommonPrepare.tapes k)) (h0 : j.val≠0) (h1 : j.val≠1)
    (i : Fin (base w r)) : prepareSlots w r k j≠firstSlots w r k i:=by
  intro he
  have hv:=congrArg Fin.val he
  have hb:=first_bound w r k i
  simp only [prepareSlots,if_neg h0,if_neg h1] at hv
  omega

theorem prepare_ne_old (w : ℕ) (r : OrdinaryOracleProgram) (k : ℕ)
    (i : Fin (base w r)) (ha : i≠address w r) (hb : i≠answer w r)
    (j : Fin (CloseoutCommonPrepare.tapes k)) :
    prepareSlots w r k j≠firstSlots w r k i:=by
  by_cases h0:j.val=0
  · rw [prepareSlots,if_pos h0,←first_address]
    exact fun he=>ha ((first_injective w r k he).symm)
  · by_cases h1:j.val=1
    · rw [prepareSlots,if_neg h0,if_pos h1]
      exact fun he=>hb ((first_injective w r k he).symm)
    · exact work_ne_first w r k j h0 h1 i

theorem middle_input (w : ℕ) (r : OrdinaryOracleProgram) (k : ℕ)
    (bits result : List Bool) (a : Fin (base w r)→List Bool)
    (ha : a (address w r)=frame bits) (hb : a (answer w r)=frame result)
    (j : Fin (CloseoutCommonPrepare.tapes k)) :
    install (firstSlots w r k) (input w r k bits) a (prepareSlots w r k j)=
      CloseoutCommonPrepare.input k bits result j:=by
  rw [prepare_input_lookup]
  by_cases h0:j.val=0
  · rw [prepareSlots,if_pos h0,←first_address,install_slot _ (first_injective w r k),if_pos h0]
    exact ha
  · by_cases h1:j.val=1
    · rw [prepareSlots,if_neg h0,if_pos h1,install_slot _ (first_injective w r k),if_neg h0,if_pos h1]
      exact hb
    · rw [install_other _ _ _ _ (fun i=>Ne.symm (work_ne_first w r k j h0 h1 i)),
        if_neg h0,if_neg h1]
      simp only [input,prepareSlots,if_neg h0,if_neg h1]
      rw [if_neg (by omega)]

end
end NearCubicWires.RepairSource.CloseoutCommonPrefix

end GR
