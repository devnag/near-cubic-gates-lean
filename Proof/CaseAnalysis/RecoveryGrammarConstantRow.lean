import Proof.CaseAnalysis.RecoveryGrammarBooleanField

/-! The original constant-node alternative keeps its inner two-value
disjunction and outer three-child conjunction in their original order. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape Composition RecoveryRootRound SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative RecoveryBoundedAddress OuterPCPRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def constantExpr {q bound : ℕ} (row : Fin (bound+1)) :=
  BoolExpr.all [tagEqualsExpr (n:=q) row 0,booleanFieldExpr (q:=q) row,secondFieldEqualsExpr (n:=q) row 0]
noncomputable def constantPrefix:=Composition.machine
  (Composition.machine (unary (first 0)) (booleanField (second 0))) (unary foldThree)
noncomputable def constantRow (next : Selection):=Composition.machine constantPrefix (fold true next)
def constantBudget (B : ℕ):=6*atomBudget B+5

theorem constant_run {q bound W C D L S B P G : ℕ}
    (room : Room W C D L S B P) (alloc : Allocation q bound G W)
    (b : BooleanDAGBuilder (descriptionWidth q bound)) (row : Fin (bound+1)) (next : Selection)
    (graphPre stackPre packet source : List Bool) (refs : List ℕ) (extra : Fin 12→List Bool)
    (valid : ValidReferences b refs W) (hg : (compileExpr b (constantExpr (q:=q) row)).final.nodes.length≤G)
    (graphSupport : ∀ d : BooleanDAGBuilder (descriptionWidth q bound),d.nodes.length≤G → (graphWord graphPre d).length≤S)
    (stackSupport : stackPre.length+W*(2*W+1)≤S) (hs : source.length≤B) (hPacket : packet.length≤B) :
    Runs (constantRow next) (constantBudget B) B P source (metadata q bound row.val C B extra)
      (originalState (selectedFields (tag 0) q bound row.val C) b graphPre stackPre packet refs)
      (originalState (selectedFields next q bound row.val C) (compileExpr b (constantExpr (q:=q) row)).final
        graphPre stackPre (ZeroPadding.pad B (selectedWord next q bound row.val C))
        (refs++[(compileExpr b (constantExpr (q:=q) row)).output.val])) := by
  let e1:=tagEqualsExpr (n:=q) row 0
  let e2:=booleanFieldExpr (q:=q) row
  let e3:=secondFieldEqualsExpr (n:=q) row 0
  let xs:=[e1,e2,e3]
  let b1:=(compileExpr b e1).final
  let b2:=(compileExpr b1 e2).final
  let b3:=(compileExpr b2 e3).final
  let refs1:=refs++[(compileExpr b e1).output.val]
  let refs2:=refs1++[(compileExpr b1 e2).output.val]
  have scalars:=alloc.scalars row
  have h3 : b3.nodes.length≤G:=(children_le_combined b true xs).trans hg
  have h2 : b2.nodes.length≤G:=(compileExpr b2 e3).extension.length_le.trans h3
  have h1 : b1.nodes.length≤G:=(compileExpr b1 e2).extension.length_le.trans h2
  have h0 : b.nodes.length≤G:=(compileExpr b e1).extension.length_le.trans h1
  have v1:=valid.after e1 (h1.trans alloc.graph)
  have v2:=v1.after e2 (h2.trans alloc.graph)
  have h6 : 6≤rowWidth q bound:=by unfold rowWidth;omega
  have hF : boundedCircuitFieldLimit q bound≤rowWidth q bound:=by unfold rowWidth;omega
  have i0:=alloc.index row 0 (Nat.zero_le _)
  have i1:=alloc.index row 6 h6
  have i2:=alloc.index row (6+boundedCircuitFieldLimit q bound) (by unfold rowWidth;omega)
  have r0:=unary_run room b row scalars (tag 0) (first 0) 0
    (graphWord graphPre b) (saved stackPre refs) packet source extra
    (by change 0+6≤rowWidth q bound;omega) rfl
    (by change row.val*rowWidth q bound+6≤W;unfold RecoveryBoundedNativeUnaryLoop.firstIndex at i0;omega)
    (by change b.nodes.length+3*6≤W;have hh:=alloc.tag;omega) (h1.trans alloc.graph)
    (graphSupport _ h0) (valid.support stackPre h0 alloc.graph stackSupport) hs hPacket
  rw [original_expression] at r0
  have r1:=booleanField_run room alloc b1 row (second 0) graphPre stackPre
    (ZeroPadding.pad B (selectedWord (first 0) q bound row.val C)) source refs1 extra
    v1 h2 graphSupport stackSupport hs (room.pad_packet_length scalars (first 0))
  have r2:=unary_run room b2 row scalars (second 0) foldThree (6+boundedCircuitFieldLimit q bound)
    (graphWord graphPre b2) (saved stackPre refs2) (ZeroPadding.pad B (selectedWord (second 0) q bound row.val C)) source extra
    (by change 6+boundedCircuitFieldLimit q bound+boundedCircuitFieldLimit q bound≤rowWidth q bound;unfold rowWidth;omega)
    (by change row.val*rowWidth q bound+6+boundedCircuitFieldLimit q bound=
      row.val*rowWidth q bound+(6+boundedCircuitFieldLimit q bound);omega)
    (by change row.val*rowWidth q bound+6+boundedCircuitFieldLimit q bound+boundedCircuitFieldLimit q bound≤W
        unfold RecoveryBoundedNativeUnaryLoop.firstIndex at i2;omega)
    (by change b2.nodes.length+3*boundedCircuitFieldLimit q bound≤W;have hh:=alloc.field;omega)
    (h3.trans alloc.graph) (graphSupport _ h2) (v2.support stackPre h2 alloc.graph stackSupport) hs
    (room.pad_packet_length scalars (second 0))
  rw [original_expression] at r2
  have prefRun:=(r0.join r1).join r2
  have forward : Runs constantPrefix (5*atomBudget B+4) B P source (metadata q bound row.val C B extra)
      (originalState (selectedFields (tag 0) q bound row.val C) b graphPre stackPre packet refs)
      (originalState (selectedFields foldThree q bound row.val C) (children b xs) graphPre stackPre
        (ZeroPadding.pad B (selectedWord foldThree q bound row.val C)) (refs++references b.nodes.length xs)) := by
    have cost : (atomBudget B+1+booleanFieldBudget B)+1+atomBudget B=5*atomBudget B+4:=by
      unfold booleanFieldBudget
      omega
    rw [cost] at prefRun
    have rrefs : refs2++[(compileExpr b2 e3).output.val]=refs++references b.nodes.length xs := by
      simp only [refs1,refs2,b1,b2,xs,references,compileExpr_output,compileExpr_length,
        List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc]
    change Runs constantPrefix (5*atomBudget B+4) B P source (metadata q bound row.val C B extra)
      (originalState (selectedFields (tag 0) q bound row.val C) b graphPre stackPre packet refs)
      (originalState (selectedFields foldThree q bound row.val C) b3 graphPre stackPre
        (ZeroPadding.pad B (selectedWord foldThree q bound row.val C))
        (refs2++[(compileExpr b2 e3).output.val])) at prefRun
    rw [rrefs] at prefRun
    exact prefRun
  have whole:=children_run room scalars constantPrefix (5*atomBudget B+4) (tag 0) foldThree next b true xs
    graphPre stackPre packet source refs extra valid hg alloc.graph graphSupport stackSupport hs rfl forward
  exact whole.more (by unfold constantBudget;omega)

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
