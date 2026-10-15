import Proof.CaseAnalysis.RecoveryGrammarNextScalars

/-! Each original row shares one paid metadata advance and next-row
selection. Graph/count/source and the saved reference stack are retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape Composition RecoveryRootRound BoundedOracleStructuralCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def afterRow (next : Selection):=Composition.machine RecoveryBoundedGrammarAdvance.focused (reselect next)
def afterRowBudget (B : ℕ):=RecoveryBoundedGrammarAdvance.budget B+1+atomBudget B

theorem afterRow_run {q bound G W C D L S B P : ℕ}
    (room : Room W C D L S B P) (alloc : Allocation q bound G W)
    (row : Fin (bound+1)) (next : Selection) (node : ℕ) (out stack packet source : List Bool)
    (extra : Fin 12→List Bool) (hPacket : packet.length≤B)
    (width : extra 0=RecoveryBoundedGrammarScalarAdd.unary B (rowWidth q bound)) :
    ∃ r,runFrom (afterRow next) (afterRowBudget B)
      (entry (afterRow next) (selectedFields foldRows q bound row.val C) node B P out stack packet source
        (metadata q bound row.val C B extra))=some r ∧
      r.steps≤afterRowBudget B ∧ r.final.heads=heads out stack ∧
      r.final.tapes=data (selectedFields next q bound (row.val+1) C) node B P out stack
        (ZeroPadding.pad B (selectedWord next q bound (row.val+1) C)) source (metadata q bound (row.val+1) C B extra) := by
  have nx:=alloc.next_scalars row
  obtain ⟨a,ar,as,ah,atapes⟩:=RecoveryBoundedGrammarAdvance.focused_run room q bound row.val extra
    (selectedFields foldRows q bound row.val C) node out stack packet source width nx.1 nx.2.1
  obtain ⟨b,br,bs,bh,bt⟩:=reselect_run room nx.2.2 foldRows next node out stack packet source extra hPacket
  have br' : runFrom (reselect next) (atomBudget B) (restart a.final (reselect next).start)=some b := by
    change runFrom _ _ ⟨_,a.final.heads,a.final.tapes⟩=some b
    rw [ah,atapes]
    exact br
  have joined:=Composition.run_join RecoveryBoundedGrammarAdvance.focused (reselect next) _ _ _ a b ar br'
  refine ⟨joinedReceipt a b,joined,?_,bh,bt⟩
  change a.steps+1+b.steps≤afterRowBudget B
  unfold afterRowBudget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
