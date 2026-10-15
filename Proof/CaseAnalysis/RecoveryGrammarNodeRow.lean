import Proof.CaseAnalysis.RecoveryGrammarConstantRow

/-! The original five node-tag alternatives compile forward, then use
exactly the original terminal-false reverse OR fold. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape Composition RecoveryRootRound SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative RecoveryBoundedAddress OuterPCPRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def nodePrefix:=Composition.machine
  (Composition.machine (Composition.machine (Composition.machine
    (constantRow (tag 1)) (addressRow 1 (tag 2))) (addressRow 2 (tag 3)))
    (doubleAddressRow 2 (tag 4))) (doubleAddressRow 2 foldFive)
noncomputable def nodeRow (next : Selection):=Composition.machine nodePrefix (fold false next)
def nodeBudget (B : ℕ):=23*atomBudget B+22

theorem node_run {q bound W C D L S B P G : ℕ}
    (room : Room W C D L S B P) (alloc : Allocation q bound G W)
    (b : BooleanDAGBuilder (descriptionWidth q bound)) (row : Fin (bound+1)) (next : Selection)
    (graphPre stackPre packet source : List Bool) (refs : List ℕ) (extra : Fin 12→List Bool)
    (valid : ValidReferences b refs W) (hg : (compileExpr b (nodeRowExpr (n:=q) row)).final.nodes.length≤G)
    (graphSupport : ∀ d : BooleanDAGBuilder (descriptionWidth q bound),d.nodes.length≤G → (graphWord graphPre d).length≤S)
    (stackSupport : stackPre.length+W*(2*W+1)≤S) (hs : source.length≤B) (hPacket : packet.length≤B) :
    Runs (nodeRow next) (nodeBudget B) B P source (metadata q bound row.val C B extra)
      (originalState (selectedFields (tag 0) q bound row.val C) b graphPre stackPre packet refs)
      (originalState (selectedFields next q bound row.val C) (compileExpr b (nodeRowExpr (n:=q) row)).final
        graphPre stackPre (ZeroPadding.pad B (selectedWord next q bound row.val C))
        (refs++[(compileExpr b (nodeRowExpr (n:=q) row)).output.val])) := by
  let e1:=constantExpr (q:=q) row
  let e2:=addressExpr (q:=q) row 1 1
  let e3:=addressExpr (q:=q) row 2 2
  let e4:=doubleAddressExpr (q:=q) row 3 2
  let e5:=doubleAddressExpr (q:=q) row 4 2
  let xs:=[e1,e2,e3,e4,e5]
  let b1:=(compileExpr b e1).final
  let b2:=(compileExpr b1 e2).final
  let b3:=(compileExpr b2 e3).final
  let b4:=(compileExpr b3 e4).final
  let b5:=(compileExpr b4 e5).final
  let refs1:=refs++[(compileExpr b e1).output.val]
  let refs2:=refs1++[(compileExpr b1 e2).output.val]
  let refs3:=refs2++[(compileExpr b2 e3).output.val]
  let refs4:=refs3++[(compileExpr b3 e4).output.val]
  have scalars:=alloc.scalars row
  have h5 : b5.nodes.length≤G:=(children_le_combined b false xs).trans hg
  have h4 : b4.nodes.length≤G:=(compileExpr b4 e5).extension.length_le.trans h5
  have h3 : b3.nodes.length≤G:=(compileExpr b3 e4).extension.length_le.trans h4
  have h2 : b2.nodes.length≤G:=(compileExpr b2 e3).extension.length_le.trans h3
  have h1 : b1.nodes.length≤G:=(compileExpr b1 e2).extension.length_le.trans h2
  have h0 : b.nodes.length≤G:=(compileExpr b e1).extension.length_le.trans h1
  have v1:=valid.after e1 (h1.trans alloc.graph)
  have v2:=v1.after e2 (h2.trans alloc.graph)
  have v3:=v2.after e3 (h3.trans alloc.graph)
  have v4:=v3.after e4 (h4.trans alloc.graph)
  have r0:=constant_run room alloc b row (tag 1) graphPre stackPre
    packet source refs extra
    valid h1 graphSupport stackSupport hs hPacket
  have r1:=address_run room alloc b1 row 1 1 (tag 2) graphPre stackPre
    (ZeroPadding.pad B (selectedWord (tag 1) q bound row.val C)) source refs1 extra
    v1 h2 graphSupport stackSupport hs (room.pad_packet_length scalars (tag 1))
  have r2:=address_run room alloc b2 row 2 2 (tag 3) graphPre stackPre
    (ZeroPadding.pad B (selectedWord (tag 2) q bound row.val C)) source refs2 extra
    v2 h3 graphSupport stackSupport hs (room.pad_packet_length scalars (tag 2))
  have r3:=doubleAddress_run room alloc b3 row 3 2 (tag 4) graphPre stackPre
    (ZeroPadding.pad B (selectedWord (tag 3) q bound row.val C)) source refs3 extra
    v3 h4 graphSupport stackSupport hs (room.pad_packet_length scalars (tag 3))
  have r4:=doubleAddress_run room alloc b4 row 4 2 foldFive graphPre stackPre
    (ZeroPadding.pad B (selectedWord (tag 4) q bound row.val C)) source refs4 extra
    v4 h5 graphSupport stackSupport hs (room.pad_packet_length scalars (tag 4))
  have prefRun:=(((r0.join r1).join r2).join r3).join r4
  have forward : Runs nodePrefix (22*atomBudget B+21) B P source (metadata q bound row.val C B extra)
      (originalState (selectedFields (tag 0) q bound row.val C) b graphPre stackPre packet refs)
      (originalState (selectedFields foldFive q bound row.val C) (children b xs) graphPre stackPre
        (ZeroPadding.pad B (selectedWord foldFive q bound row.val C)) (refs++references b.nodes.length xs)) := by
    have cost : (((constantBudget B+1+paddingBudget B)+1+paddingBudget B)+1+paddingBudget B)+1+
        paddingBudget B=22*atomBudget B+21:=by
      unfold constantBudget paddingBudget
      omega
    rw [cost] at prefRun
    have rrefs : refs4++[(compileExpr b4 e5).output.val]=refs++references b.nodes.length xs := by
      simp only [refs1,refs2,refs3,refs4,b1,b2,b3,b4,xs,references,compileExpr_output,compileExpr_length,
        List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc]
    change Runs nodePrefix (22*atomBudget B+21) B P source (metadata q bound row.val C B extra)
      (originalState (selectedFields (tag 0) q bound row.val C) b graphPre stackPre packet refs)
      (originalState (selectedFields foldFive q bound row.val C) b5 graphPre stackPre
        (ZeroPadding.pad B (selectedWord foldFive q bound row.val C))
        (refs4++[(compileExpr b4 e5).output.val])) at prefRun
    rw [rrefs] at prefRun
    exact prefRun
  have whole:=children_run room scalars nodePrefix (22*atomBudget B+21) (tag 0) foldFive next b false xs
    graphPre stackPre packet source refs extra valid hg alloc.graph graphSupport stackSupport hs rfl forward
  exact whole.more (by unfold nodeBudget;omega)

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
