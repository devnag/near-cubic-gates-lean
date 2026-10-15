import Proof.CaseAnalysis.RecoveryGrammarDoubleAddressRow

/-! The original constant-node alternative admits the two unary Boolean
values by a literal two-child disjunction, including its final false gate. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape Composition RecoveryRootRound SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative RecoveryBoundedAddress OuterPCPRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def booleanFieldExpr {q bound : ℕ} (row : Fin (bound+1)) :=
  BoolExpr.any [firstFieldEqualsExpr (n:=q) row 0,firstFieldEqualsExpr (n:=q) row 1]
noncomputable def booleanFieldPrefix:=Composition.machine (unary (first 1)) (unary foldTwo)
noncomputable def booleanField (next : Selection):=Composition.machine booleanFieldPrefix (fold false next)
def booleanFieldBudget (B : ℕ):=3*atomBudget B+2

theorem booleanField_run {q bound W C D L S B P G : ℕ}
    (room : Room W C D L S B P) (alloc : Allocation q bound G W)
    (b : BooleanDAGBuilder (descriptionWidth q bound)) (row : Fin (bound+1)) (next : Selection)
    (graphPre stackPre packet source : List Bool) (refs : List ℕ) (extra : Fin 12→List Bool)
    (valid : ValidReferences b refs W) (hg : (compileExpr b (booleanFieldExpr (q:=q) row)).final.nodes.length≤G)
    (graphSupport : ∀ d : BooleanDAGBuilder (descriptionWidth q bound),d.nodes.length≤G → (graphWord graphPre d).length≤S)
    (stackSupport : stackPre.length+W*(2*W+1)≤S) (hs : source.length≤B) (hPacket : packet.length≤B) :
    Runs (booleanField next) (booleanFieldBudget B) B P source (metadata q bound row.val C B extra)
      (originalState (selectedFields (first 0) q bound row.val C) b graphPre stackPre packet refs)
      (originalState (selectedFields next q bound row.val C) (compileExpr b (booleanFieldExpr (q:=q) row)).final
        graphPre stackPre (ZeroPadding.pad B (selectedWord next q bound row.val C))
        (refs++[(compileExpr b (booleanFieldExpr (q:=q) row)).output.val])) := by
  let e1:=firstFieldEqualsExpr (n:=q) row 0
  let e2:=firstFieldEqualsExpr (n:=q) row 1
  let xs:=[e1,e2]
  let b1:=(compileExpr b e1).final
  let b2:=(compileExpr b1 e2).final
  let refs1:=refs++[(compileExpr b e1).output.val]
  have scalars:=alloc.scalars row
  have h2 : b2.nodes.length≤G:=(children_le_combined b false xs).trans hg
  have h1 : b1.nodes.length≤G:=(compileExpr b1 e2).extension.length_le.trans h2
  have h0 : b.nodes.length≤G:=(compileExpr b e1).extension.length_le.trans h1
  have v1:=valid.after e1 (h1.trans alloc.graph)
  have i1:=alloc.index row 6 (by unfold rowWidth;omega)
  have hindex : row.val*rowWidth q bound+6+boundedCircuitFieldLimit q bound≤W := by
    unfold RecoveryBoundedNativeUnaryLoop.firstIndex at i1
    have hF : boundedCircuitFieldLimit q bound≤rowWidth q bound:=by unfold rowWidth;omega
    omega
  have r0:=unary_run room b row scalars (first 0) (first 1) 6
    (graphWord graphPre b) (saved stackPre refs) packet source extra
    (by change 6+boundedCircuitFieldLimit q bound≤rowWidth q bound;unfold rowWidth;omega) rfl
    hindex (by change b.nodes.length+3*boundedCircuitFieldLimit q bound≤W;have hh:=alloc.field;omega)
    (h1.trans alloc.graph) (graphSupport _ h0) (valid.support stackPre h0 alloc.graph stackSupport) hs hPacket
  rw [original_expression] at r0
  have r1:=unary_run room b1 row scalars (first 1) foldTwo 6
    (graphWord graphPre b1) (saved stackPre refs1) (ZeroPadding.pad B (selectedWord (first 1) q bound row.val C)) source extra
    (by change 6+boundedCircuitFieldLimit q bound≤rowWidth q bound;unfold rowWidth;omega) rfl
    hindex (by change b1.nodes.length+3*boundedCircuitFieldLimit q bound≤W;have hh:=alloc.field;omega)
    (h2.trans alloc.graph) (graphSupport _ h1) (v1.support stackPre h1 alloc.graph stackSupport) hs
    (room.pad_packet_length scalars (first 1))
  rw [original_expression] at r1
  have prefRun:=r0.join r1
  have forward : Runs booleanFieldPrefix (2*atomBudget B+1) B P source (metadata q bound row.val C B extra)
      (originalState (selectedFields (first 0) q bound row.val C) b graphPre stackPre packet refs)
      (originalState (selectedFields foldTwo q bound row.val C) (children b xs) graphPre stackPre
        (ZeroPadding.pad B (selectedWord foldTwo q bound row.val C)) (refs++references b.nodes.length xs)) := by
    have cost : atomBudget B+1+atomBudget B=2*atomBudget B+1:=by omega
    rw [cost] at prefRun
    have rrefs : refs1++[(compileExpr b1 e2).output.val]=refs++references b.nodes.length xs := by
      simp only [refs1,b1,xs,references,compileExpr_output,compileExpr_length,
        List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc]
    change Runs booleanFieldPrefix (2*atomBudget B+1) B P source (metadata q bound row.val C B extra)
      (originalState (selectedFields (first 0) q bound row.val C) b graphPre stackPre packet refs)
      (originalState (selectedFields foldTwo q bound row.val C) b2 graphPre stackPre
        (ZeroPadding.pad B (selectedWord foldTwo q bound row.val C))
        (refs1++[(compileExpr b1 e2).output.val])) at prefRun
    rw [rrefs] at prefRun
    exact prefRun
  have whole:=children_run room scalars booleanFieldPrefix (2*atomBudget B+1) (first 0) foldTwo next b false xs
    graphPre stackPre packet source refs extra valid hg alloc.graph graphSupport stackSupport hs rfl forward
  exact whole.more (by unfold booleanFieldBudget;omega)

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
