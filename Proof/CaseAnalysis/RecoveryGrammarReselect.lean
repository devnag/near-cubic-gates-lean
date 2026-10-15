import Proof.CaseAnalysis.RecoveryGrammarAdvanceDock

/-! A paid row-boundary packet print and work-bank reload selects the
first atom of the next original row while retaining graph/count/stack. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def reselect (next : Selection):=prepared next RecoveryBoundedGrammarReload.machine

theorem reselect_run {q bound row W C D L S B P : ℕ}
    (room : Room W C D L S B P) (scalars : ScalarFits q bound row W)
    (current next : Selection) (node : ℕ) (out stack packet source : List Bool) (extra : Fin 12→List Bool)
    (hPacket : packet.length≤B) :
    Runs (reselect next) (atomBudget B) B P source (metadata q bound row C B extra)
      ⟨selectedFields current q bound row C,node,out,stack,packet⟩
      ⟨selectedFields next q bound row C,node,out,stack,ZeroPadding.pad B (selectedWord next q bound row C)⟩ := by
  let fields:=selectedFields current q bound row C
  let nextFields:=selectedFields next q bound row C
  let nextWord:=selectedWord next q bound row C
  let tail:=List.replicate (B-nextWord.length) false
  have cr:=room.packet_fits scalars current
  have nr:=room.packet_fits scalars next
  obtain ⟨r,rr,rs,rh,rt⟩:=RecoveryBoundedGrammarReload.padded_run fields nextFields node B P
    out stack tail source cr.2.2.2.2.2.2 nr.2.2.2.2.2.2 nr.2.2.2.2.2.1
  have whole : Runs (reselect next)
      (preparedBudget C (rowIndex q bound row next.index) next.value.val (rowLimit q bound next.limit)
        (rowUpper q row next.upper) B (RecoveryBoundedGrammarReload.budget nextFields B))
      B P source (metadata q bound row C B extra)
      ⟨fields,node,out,stack,packet⟩
      ⟨nextFields,node,out,stack,ZeroPadding.pad B nextWord⟩ := by
    exact prepared_run RecoveryBoundedGrammarReload.machine next C (rowIndex q bound row next.index)
      next.value.val (rowLimit q bound next.limit) (rowUpper q row next.upper) B P
      (RecoveryBoundedGrammarReload.budget nextFields B) fields node node out stack packet out stack source
      (metadata q bound row C B extra)
      (metadata_scalar next q bound row C B P node fields out stack packet source extra)
      hPacket nr.1 nr.2.1 nr.2.2.1 nr.2.2.2.1 nr.2.2.2.2.1 nr.2.2.2.2.2.1 r rr rs rh rt
  apply whole.more
  have upper:=room.atom_budget scalars next 0 0 (Nat.zero_le _) (Nat.zero_le _)
  unfold preparedBudget RecoveryBoundedGrammarReload.budget RecoveryBoundedGrammarAfter.budget at *
  dsimp only [nextFields] at *
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
