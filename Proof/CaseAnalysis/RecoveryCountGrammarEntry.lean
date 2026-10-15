import Proof.CaseAnalysis.RecoveryCountScalarReset
import Proof.CaseAnalysis.RecoveryGrammarReselect

/-! Start the next original grammar directly from the existing row bank.
The accepted printer and erase/reload worker physically install tag zero. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountGrammarEntry
open LocalBitMultitape RecoveryRootRound
open RecoveryBoundedGrammarCold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=reselect (tag 0)

theorem run {q bound W C D L S B P : ℕ}
    (room : Room W C D L S B P) (scalars : ScalarFits q bound 0 W)
    (current : Fin 78→List Bool) (node : ℕ) (out stack packet source : List Bool)
    (extra : Fin 12→List Bool) (hPacket : packet.length≤B)
    (hc : ∀ j∈RecoveryBoundedRowReload.ports,(current j).length≤B) :
    Runs machine (atomBudget B) B P source (metadata q bound 0 C B extra)
      ⟨current,node,out,stack,packet⟩
      ⟨selectedFields (tag 0) q bound 0 C,node,out,stack,
        ZeroPadding.pad B (selectedWord (tag 0) q bound 0 C)⟩ := by
  let next:=tag 0
  let nextFields:=selectedFields next q bound 0 C
  let nextWord:=selectedWord next q bound 0 C
  let tail:=List.replicate (B-nextWord.length) false
  have nr:=room.packet_fits scalars next
  obtain ⟨r,rr,rs,rh,rt⟩:=RecoveryBoundedGrammarReload.padded_run current nextFields node B P
    out stack tail source hc nr.2.2.2.2.2.2 nr.2.2.2.2.2.1
  have whole : Runs machine
      (preparedBudget C (rowIndex q bound 0 next.index) next.value.val (rowLimit q bound next.limit)
        (rowUpper q 0 next.upper) B (RecoveryBoundedGrammarReload.budget nextFields B))
      B P source (metadata q bound 0 C B extra)
      ⟨current,node,out,stack,packet⟩
      ⟨nextFields,node,out,stack,ZeroPadding.pad B nextWord⟩ := by
    exact prepared_run RecoveryBoundedGrammarReload.machine next C (rowIndex q bound 0 next.index)
      next.value.val (rowLimit q bound next.limit) (rowUpper q 0 next.upper) B P
      (RecoveryBoundedGrammarReload.budget nextFields B) current node node out stack packet out stack source
      (metadata q bound 0 C B extra)
      (metadata_scalar next q bound 0 C B P node current out stack packet source extra)
      hPacket nr.1 nr.2.1 nr.2.2.1 nr.2.2.2.1 nr.2.2.2.2.1 nr.2.2.2.2.2.1 r rr rs rh rt
  apply whole.more
  have upper:=room.atom_budget scalars next 0 0 (Nat.zero_le _) (Nat.zero_le _)
  unfold preparedBudget RecoveryBoundedGrammarReload.budget RecoveryBoundedGrammarAfter.budget at *
  dsimp only [nextFields] at *
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountGrammarEntry
