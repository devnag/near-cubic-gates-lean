import Proof.CaseAnalysis.CommonProgramOnePorts
import Proof.Amplification.RecoveryCaseOnePaddedBitInput
import Proof.CaseAnalysis.CommonPortBankAt

/-! Case1 consumes the retained hierarchy request and final address with
the physically cleared common query. Padding preserves its actual run. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def oneColdInput (p : Parameters) (word bits : List Bool) : Fin (on p)→List Bool:=
  RecoveryCaseOnePaddedBit.input (source p) (amp p) p.k word bits
def oneInput (p : Parameters) (word bits : List Bool) (capacity : ℕ):=
  Function.update (oneColdInput p word bits) (one p).queryTape (List.replicate capacity false)
def oneCaps (p : Parameters) (capacity : ℕ) (i : Fin (on p)):=
  if i=(one p).queryTape then capacity else 0

theorem one_query_empty (p : Parameters) (word bits : List Bool) :
    oneColdInput p word bits (one p).queryTape=[]:=by
  have hq:=(one p).queryFresh
  have hb:(one p).queryTape.val<RecoveryCaseOnePaddedBit.base (source p) (amp p) p.k:=
    (RecoveryCaseOneHierarchy.ports (source p) (amp p) p.k).queryTape.isLt
  rw [oneColdInput,RecoveryCaseOnePaddedBit.input_lookup,if_neg hq,if_neg (by omega)]

theorem one_input_padding (p : Parameters) (word bits : List Bool) (capacity : ℕ) :
    (fun i=>ZeroPadding.pad (oneCaps p capacity i) (oneColdInput p word bits i))=
      oneInput p word bits capacity:=by
  funext i
  by_cases hi:i=(one p).queryTape
  · subst i
    simp only [oneCaps,if_true,one_query_empty,ZeroPadding.pad,List.length_nil,Nat.sub_zero,
      List.nil_append,oneInput,Function.update_self]
  · simp only [oneCaps,if_neg hi,ZeroPadding.pad_zero,oneInput,Function.update_of_ne hi]

theorem one_input_empty (p : Parameters) (word bits : List Bool) (capacity : ℕ)
    (i : Fin (on p)) (hi : ∀ j,oneLocal p j≠i) : oneInput p word bits capacity i=[]:=by
  have hq:i≠(one p).queryTape:=(hi 2).symm
  have h0:i.val≠0:=by intro h;exact hi 0 (Fin.ext h.symm)
  have ha:i.val≠RecoveryCaseOnePaddedBit.base (source p) (amp p) p.k+16:=by
    intro h
    exact hi 1 (Fin.ext h.symm)
  rw [oneInput,Function.update_of_ne hq,oneColdInput,RecoveryCaseOnePaddedBit.input_lookup,
    if_neg h0,if_neg ha]

theorem one_padded_ready (p : Parameters) (word bits : List Bool) (capacity fuel : ℕ)
    (out : Fin (on p)→List Bool)
    (actual : Ready RecoveryOracle.correctedSat (one p) fuel (oneColdInput p word bits) out) :
    ∃ padded,Ready RecoveryOracle.correctedSat (one p) fuel (oneInput p word bits capacity) padded ∧
      padded (one p).base.outputTape=out (one p).base.outputTape:=by
  have h:=Ready.padding actual (oneCaps p capacity)
  have hi:=one_input_padding p word bits capacity
  have hr:Ready RecoveryOracle.correctedSat (one p) fuel (oneInput p word bits capacity)
      (fun i=>ZeroPadding.pad (oneCaps p capacity i) (out i)):=hi ▸ h
  have hq:(one p).base.outputTape≠(one p).queryTape:=by
    intro he
    exact (by decide : (3 : Fin 4)≠2) (one_local_injective p he)
  refine ⟨_,hr,?_⟩
  exact (congrArg (fun c=>ZeroPadding.pad c (out (one p).base.outputTape))
    (if_neg hq)).trans (ZeroPadding.pad_zero _)

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
