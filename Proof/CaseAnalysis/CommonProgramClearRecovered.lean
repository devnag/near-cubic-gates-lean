import Proof.CaseAnalysis.CommonProgramClearInput
import Proof.CaseAnalysis.CommonProgramRecoveryFresh
import Proof.CaseAnalysis.CommonProgramRecoveredQuery

/-! The paid clear receives the actual post-recovery query, retained final
address, and unused private work tapes. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

private theorem two_heads (f : Fin 2→ℕ) (h0 : f 0=0) (h1 : f 1=0) : ∀ j,f j=0:=by
  intro j
  fin_cases j
  · exact h0
  · exact h1

theorem clear_recovered_entry (p : Parameters) (bits : List Bool) (padding : ℕ)
    (out : Fin (prefixProgram p).base.tapeCount→List Bool) (final : (recovery p).Config)
    (ha : out ⟨0,(prefixProgram p).base.twoTapes.trans_lt' (by decide)⟩=frame bits)
    (hq : final.heads (RecoveryBoundedCold.queryPort (source p) p.k p.degree)=0) :
    let c:=recovered p bits out padding final
    (∀ i,c.tapes (clearSlot p i)=
      CloseoutCommonQueryClear.input bits (c.tapes (ports p).queryTape) i) ∧
      (∀ i,c.heads (clearSlot p i)=0):=by
  let c:=recovered p bits out padding final
  let query:=c.tapes (ports p).queryTape
  have addr:=recovered_address p bits out padding final ha
  have local_words : ∀ j,c.tapes (clearSlot p (clearLocal j))=
      CloseoutCommonQueryClear.input bits query (clearLocal j):=by
    intro j
    fin_cases j
    · exact ((congrArg c.tapes (clear_address p)).trans addr.2).trans
        (clear_input_fields bits query 0).symm
    · exact (congrArg c.tapes (clear_query p)).trans
        (clear_input_fields bits query 1).symm
  have local_heads : ∀ j,c.heads (clearSlot p (clearLocal j))=0:=
    two_heads (fun j=>c.heads (clearSlot p (clearLocal j)))
      ((congrArg c.heads (clear_address p)).trans addr.1)
      ((congrArg c.heads (clear_query p)).trans
        (recovered_query_head p bits out padding final hq))
  have boundary (i : Fin 28) : n1 p ≤ (lift2 p (i.natAdd (n1 p))).val:=by
    simp only [lift2,Fin.val_castAdd,Fin.val_natAdd]
    exact Nat.le_add_right _ _
  refine ⟨clear_entry p bits query c.tapes ?_ ?_,clear_entry_heads p c.heads ?_ ?_⟩
  · intro j
    exact (congrArg c.tapes (clear_inputs p j).symm).trans (local_words j)
  · intro i
    exact (recovered_fresh p bits out padding final _ (boundary i)).2
  · intro j
    exact (congrArg c.heads (clear_inputs p j).symm).trans (local_heads j)
  · intro i
    exact (recovered_fresh p bits out padding final _ (boundary i)).1

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
