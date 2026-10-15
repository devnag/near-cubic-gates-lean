import Proof.CaseAnalysis.RecoveryGrammarAfterRow

/-! Join each literal original row to the same paid next-row continuation. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape Composition RecoveryRootRound SourceInterfaces
open BoundedOracleStructuralCircuit FinitePredicateCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {s : ℕ}
noncomputable def rowBody (p : Machine 112 s) (next : Selection):=Composition.machine p (afterRow next)
def rowBodyBudget (fuel B : ℕ):=fuel+1+afterRowBudget B
noncomputable def nodeBody:=rowBody (nodeRow foldRows) (tag 0)
noncomputable def paddingBody:=rowBody (padding foldRows) (tag 6)
noncomputable def outputBody:=rowBody (addressRow 2 foldRows) (tag 6)

theorem rowBody_run {q bound G W C D L S B P : ℕ}
    (room : Room W C D L S B P) (alloc : Allocation q bound G W)
    (p : Machine 112 s) (fuel : ℕ) (b : BooleanDAGBuilder (descriptionWidth q bound))
    (row : Fin (bound+1)) (e : BoolExpr (descriptionWidth q bound)) (current next : Selection)
    (graphPre stackPre packet source : List Bool) (refs : List ℕ) (extra : Fin 12→List Bool)
    (width : extra 0=RecoveryBoundedGrammarScalarAdd.unary B (rowWidth q bound))
    (core : Runs p fuel B P source (metadata q bound row.val C B extra)
      (originalState (selectedFields current q bound row.val C) b graphPre stackPre packet refs)
      (originalState (selectedFields foldRows q bound row.val C) (compileExpr b e).final graphPre stackPre
        (ZeroPadding.pad B (selectedWord foldRows q bound row.val C)) (refs++[(compileExpr b e).output.val]))) :
    ∃ r,runFrom (rowBody p next) (rowBodyBudget fuel B)
      ((originalState (selectedFields current q bound row.val C) b graphPre stackPre packet refs).configuration
        (rowBody p next) B P source (metadata q bound row.val C B extra))=some r ∧
      r.steps≤rowBodyBudget fuel B ∧
      r.final.heads=heads (graphWord graphPre (compileExpr b e).final) (saved stackPre (refs++[(compileExpr b e).output.val])) ∧
      r.final.tapes=data (selectedFields next q bound (row.val+1) C) (compileExpr b e).final.nodes.length B P
        (graphWord graphPre (compileExpr b e).final) (saved stackPre (refs++[(compileExpr b e).output.val]))
        (ZeroPadding.pad B (selectedWord next q bound (row.val+1) C)) source (metadata q bound (row.val+1) C B extra) := by
  obtain ⟨a,ar,as,ah,atapes⟩:=core
  obtain ⟨z,zr,zs,zh,zt⟩:=afterRow_run room alloc row next (compileExpr b e).final.nodes.length
    (graphWord graphPre (compileExpr b e).final) (saved stackPre (refs++[(compileExpr b e).output.val]))
    (ZeroPadding.pad B (selectedWord foldRows q bound row.val C)) source extra
    (room.pad_packet_length (alloc.scalars row) foldRows) width
  have zr' : runFrom (afterRow next) (afterRowBudget B) (restart a.final (afterRow next).start)=some z := by
    change runFrom _ _ ⟨_,a.final.heads,a.final.tapes⟩=some z
    rw [ah,atapes]
    exact zr
  have joined:=Composition.run_join p (afterRow next) _ _ _ a z ar zr'
  refine ⟨joinedReceipt a z,joined,?_,zh,zt⟩
  change a.steps+1+z.steps≤rowBodyBudget fuel B
  unfold rowBodyBudget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
