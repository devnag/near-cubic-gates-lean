import Proof.CaseAnalysis.RecoveryGrammarAddressRow

/-! The original AND and OR alternatives compile both strict predecessor
fields, preserving the same tag/first/second graph order. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape Composition RecoveryRootRound SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative RecoveryBoundedAddress OuterPCPRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def doubleAddressExpr {q bound : ℕ} (row : Fin (bound+1)) (value : Fin 7) (upper : Fin 3) :=
  BoolExpr.all [tagEqualsExpr (n:=q) row value.val,
    firstFieldLessExpr (n:=q) row (rowUpper q row.val upper),secondFieldLessExpr (n:=q) row (rowUpper q row.val upper)]
noncomputable def doubleAddressPrefix (upper : Fin 3):=Composition.machine
  (Composition.machine (unary (firstLess upper)) (less (secondLess upper))) (less foldThree)
noncomputable def doubleAddressRow (upper : Fin 3) (next : Selection):=Composition.machine (doubleAddressPrefix upper) (fold true next)

theorem doubleAddress_run {q bound W C D L S B P G : ℕ}
    (room : Room W C D L S B P) (alloc : Allocation q bound G W)
    (b : BooleanDAGBuilder (descriptionWidth q bound)) (row : Fin (bound+1)) (value : Fin 7) (upper : Fin 3) (next : Selection)
    (graphPre stackPre packet source : List Bool) (refs : List ℕ) (extra : Fin 12→List Bool)
    (valid : ValidReferences b refs W) (hg : (compileExpr b (doubleAddressExpr (q:=q) row value upper)).final.nodes.length≤G)
    (graphSupport : ∀ d : BooleanDAGBuilder (descriptionWidth q bound),d.nodes.length≤G → (graphWord graphPre d).length≤S)
    (stackSupport : stackPre.length+W*(2*W+1)≤S) (hs : source.length≤B) (hPacket : packet.length≤B) :
    Runs (doubleAddressRow upper next) (paddingBudget B) B P source (metadata q bound row.val C B extra)
      (originalState (selectedFields (tag value) q bound row.val C) b graphPre stackPre packet refs)
      (originalState (selectedFields next q bound row.val C) (compileExpr b (doubleAddressExpr (q:=q) row value upper)).final
        graphPre stackPre (ZeroPadding.pad B (selectedWord next q bound row.val C))
        (refs++[(compileExpr b (doubleAddressExpr (q:=q) row value upper)).output.val])) := by
  let e1:=tagEqualsExpr (n:=q) row value.val
  let e2:=firstFieldLessExpr (n:=q) row (rowUpper q row.val upper)
  let e3:=secondFieldLessExpr (n:=q) row (rowUpper q row.val upper)
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
  have upperBound : rowUpper q row.val upper≤boundedCircuitFieldLimit q bound := by
    have hr:=row.isLt
    fin_cases upper <;> simp [rowUpper,boundedCircuitFieldLimit] <;> omega
  have upperCost:=Nat.mul_le_mul_right (3*boundedCircuitFieldLimit q bound+1) upperBound
  have i0:=alloc.index row 0 (Nat.zero_le _)
  have i1:=alloc.index row 6 h6
  have i2:=alloc.index row (6+boundedCircuitFieldLimit q bound) (by unfold rowWidth;omega)
  have r0:=unary_run room b row scalars (tag value) (firstLess upper) 0
    (graphWord graphPre b) (saved stackPre refs) packet source extra
    (by change 0+6≤rowWidth q bound;omega) rfl
    (by change row.val*rowWidth q bound+6≤W;unfold RecoveryBoundedNativeUnaryLoop.firstIndex at i0;omega)
    (by change b.nodes.length+3*6≤W;have hh:=alloc.tag;omega) (h1.trans alloc.graph)
    (graphSupport _ h0) (valid.support stackPre h0 alloc.graph stackSupport) hs hPacket
  rw [original_expression] at r0
  have r1:=less_run room b1 row scalars (firstLess upper) (secondLess upper) 6
    (graphWord graphPre b1) (saved stackPre refs1) (ZeroPadding.pad B (selectedWord (firstLess upper) q bound row.val C)) source extra
    (by change 6+boundedCircuitFieldLimit q bound≤rowWidth q bound;unfold rowWidth;omega) rfl rfl
    (by change row.val*rowWidth q bound+6+boundedCircuitFieldLimit q bound≤W
        unfold RecoveryBoundedNativeUnaryLoop.firstIndex at i1;omega)
    (by change b1.nodes.length+rowUpper q row.val upper*(3*boundedCircuitFieldLimit q bound+1)+
      3*boundedCircuitFieldLimit q bound≤W;have hh:=alloc.less;omega)
    (h2.trans alloc.graph) (graphSupport _ h1) (v1.support stackPre h1 alloc.graph stackSupport) hs
    (room.pad_packet_length scalars (firstLess upper))
  rw [original_expression] at r1
  have r2:=less_run room b2 row scalars (secondLess upper) foldThree (6+boundedCircuitFieldLimit q bound)
    (graphWord graphPre b2) (saved stackPre refs2) (ZeroPadding.pad B (selectedWord (secondLess upper) q bound row.val C)) source extra
    (by change 6+boundedCircuitFieldLimit q bound+boundedCircuitFieldLimit q bound≤rowWidth q bound;unfold rowWidth;omega)
    (by change row.val*rowWidth q bound+6+boundedCircuitFieldLimit q bound=
      row.val*rowWidth q bound+(6+boundedCircuitFieldLimit q bound);omega) rfl
    (by change row.val*rowWidth q bound+6+boundedCircuitFieldLimit q bound+boundedCircuitFieldLimit q bound≤W
        unfold RecoveryBoundedNativeUnaryLoop.firstIndex at i2;omega)
    (by change b2.nodes.length+rowUpper q row.val upper*(3*boundedCircuitFieldLimit q bound+1)+
      3*boundedCircuitFieldLimit q bound≤W;have hh:=alloc.less;omega)
    (h3.trans alloc.graph) (graphSupport _ h2) (v2.support stackPre h2 alloc.graph stackSupport) hs
    (room.pad_packet_length scalars (secondLess upper))
  rw [original_expression] at r2
  have prefRun:=(r0.join r1).join r2
  have forward : Runs (doubleAddressPrefix upper) (3*atomBudget B+2) B P source (metadata q bound row.val C B extra)
      (originalState (selectedFields (tag value) q bound row.val C) b graphPre stackPre packet refs)
      (originalState (selectedFields foldThree q bound row.val C) (children b xs) graphPre stackPre
        (ZeroPadding.pad B (selectedWord foldThree q bound row.val C)) (refs++references b.nodes.length xs)) := by
    have cost : (atomBudget B+1+atomBudget B)+1+atomBudget B=3*atomBudget B+2:=by omega
    rw [cost] at prefRun
    have rrefs : refs2++[(compileExpr b2 e3).output.val]=refs++references b.nodes.length xs := by
      simp only [refs1,refs2,b1,b2,xs,references,compileExpr_output,compileExpr_length,
        List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc]
    change Runs (doubleAddressPrefix upper) (3*atomBudget B+2) B P source (metadata q bound row.val C B extra)
      (originalState (selectedFields (tag value) q bound row.val C) b graphPre stackPre packet refs)
      (originalState (selectedFields foldThree q bound row.val C) b3 graphPre stackPre
        (ZeroPadding.pad B (selectedWord foldThree q bound row.val C))
        (refs2++[(compileExpr b2 e3).output.val])) at prefRun
    rw [rrefs] at prefRun
    exact prefRun
  have whole:=children_run room scalars (doubleAddressPrefix upper) (3*atomBudget B+2) (tag value) foldThree next b true xs
    graphPre stackPre packet source refs extra valid hg alloc.graph graphSupport stackSupport hs rfl forward
  exact whole.more (by unfold paddingBudget;omega)

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
