import Proof.CaseAnalysis.RecoveryGrammarFinishScan

/-! The two scans and the one output row execute the original complete
forward grammar sequence. The terminal reverse conjunction is the next consumer. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape Composition SourceInterfaces FinitePredicateCircuit BoundedOracleStructuralCircuit
open RecoveryBoundedNative RecoveryBoundedAddress
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def forward:=Composition.machine (Composition.machine nodeScan outputScan) paddingScan
def forwardBudget (B bound count : ℕ):=(nodeScanBudget B count+1+outputScanBudget B)+1+paddingScanBudget B bound count

theorem path_entry {s q bound : ℕ} (p : Machine 112 s) (b : BooleanDAGBuilder (descriptionWidth q bound))
    (xs : List (BoolExpr (descriptionWidth q bound))) (current : Selection) (first C B P : ℕ)
    (graphPre stackPre source : List Bool) (refs : List ℕ) (extra : Fin 12→List Bool) :
    pathConfig p b xs current first C B P graphPre stackPre source refs extra 0=
      (originalState (selectedFields current q bound first C) b graphPre stackPre
        (ZeroPadding.pad B (selectedWord current q bound first C)) refs).configuration p B P source
        (metadata q bound first C B extra) := by
  unfold pathConfig
  rw [pathState_zero]
  rfl

theorem forward_run {q bound G W C D L S B P : ℕ}
    (room : Room W C D L S B P) (alloc : Allocation q bound G W)
    (b : BooleanDAGBuilder (descriptionWidth q bound)) (count : Fin bound)
    (graphPre stackPre source : List Bool) (refs : List ℕ) (extra : Fin 12→List Bool)
    (valid : ValidReferences b refs W)
    (hg : (compileExpr b (fixedCountGrammarExpr (n:=q) count)).final.nodes.length≤G)
    (graphSupport : ∀ d : BooleanDAGBuilder (descriptionWidth q bound),d.nodes.length≤G → (graphWord graphPre d).length≤S)
    (stackSupport : stackPre.length+W*(2*W+1)≤S) (hs : source.length≤B)
    (width : extra 0=RecoveryBoundedGrammarScalarAdd.unary B (rowWidth q bound)) :
    let before:=originalState (selectedFields (tag 0) q bound 0 C) b graphPre stackPre
      (ZeroPadding.pad B (selectedWord (tag 0) q bound 0 C)) refs
    let after:=originalState (selectedFields (tag 6) q bound (bound+1) C)
      (children b (RecoveryBoundedGrammar.rows (q:=q) count)) graphPre stackPre
      (ZeroPadding.pad B (selectedWord (tag 6) q bound (bound+1) C))
      (refs++references b.nodes.length (RecoveryBoundedGrammar.rows (q:=q) count))
    ∃ r,runFrom forward (forwardBudget B bound count.val)
      ⟨forward.start,scanHeads (heads before.out before.stack) 1 1,
        scanData (data before.fields before.node B P before.out before.stack before.packet source
          (metadata q bound 0 C B extra)) B bound count.val⟩=some r ∧
      r.steps≤forwardBudget B bound count.val ∧ r.final.heads=scanHeads (heads after.out after.stack) 1 1 ∧
      r.final.tapes=scanData (data after.fields after.node B P after.out after.stack after.packet source
        (metadata q bound (bound+1) C B extra)) B bound count.val := by
  let bn:=children b (countNodeRows (n:=q) count)
  let e:=outputRowExpr (n:=q) (⟨count.val+1,by omega⟩ : Fin (bound+1))
  let bo:=(compileExpr bn e).final
  let rn:=refs++references b.nodes.length (countNodeRows (n:=q) count)
  let ro:=rn++[(compileExpr bn e).output.val]
  have allChildren : children b (RecoveryBoundedGrammar.rows (q:=q) count)=children bo (countPaddingRows (n:=q) count) := by
    rw [RecoveryBoundedGrammar.rows,children_append]
    rfl
  have hp : (children bo (countPaddingRows (n:=q) count)).nodes.length≤G := by
    rw [←allChildren]
    exact (children_le_combined b true (RecoveryBoundedGrammar.rows (q:=q) count)).trans hg
  have ho : bo.nodes.length≤G := by rw [children_length] at hp;omega
  have hn : bn.nodes.length≤G:=(compileExpr bn e).extension.length_le.trans ho
  have vn:=valid.children (countNodeRows (n:=q) count) hn alloc.graph
  have vo:=vn.after e (ho.trans alloc.graph)
  obtain ⟨a,ar,as,ah,atapes⟩:=nodeScan_run room alloc b count graphPre stackPre source refs extra
    valid hn graphSupport stackSupport hs width
  rw [path_entry] at ar
  have tn : (countNodeRows (n:=q) count).take (count.val+1)=countNodeRows (n:=q) count :=
    List.take_of_length_le (by simp only [countNodeRows,List.length_ofFn];omega)
  have ah' : a.final.heads=scanHeads (heads (graphWord graphPre bn) (saved stackPre rn)) (count.val+2) 1 := by
    simpa only [pathConfig,pathState,RowState.configuration,entry,originalState,tn,Nat.zero_add] using ah
  have at' : a.final.tapes=scanData (data (selectedFields (tag 0) q bound (count.val+1) C) bn.nodes.length B P
      (graphWord graphPre bn) (saved stackPre rn) (ZeroPadding.pad B (selectedWord (tag 0) q bound (count.val+1) C))
      source (metadata q bound (count.val+1) C B extra)) B bound count.val := by
    simpa only [pathConfig,pathState,RowState.configuration,entry,originalState,tn,Nat.zero_add] using atapes
  obtain ⟨o,orr,os,oh,ot⟩:=outputScan_run room alloc bn count graphPre stackPre source rn extra
    vn ho graphSupport stackSupport hs width
  have or' : runFrom outputScan (outputScanBudget B) (restart a.final outputScan.start)=some o := by
    change runFrom _ _ ⟨_,a.final.heads,a.final.tapes⟩=some o
    rw [ah',at']
    exact orr
  obtain ⟨p,pr,ps,ph,pt⟩:=paddingScan_run room alloc bo count graphPre stackPre source ro extra
    vo hp graphSupport stackSupport hs width
  rw [path_entry] at pr
  have pr' : runFrom paddingScan (paddingScanBudget B bound count.val) (restart o.final paddingScan.start)=some p := by
    change runFrom _ _ ⟨_,o.final.heads,o.final.tapes⟩=some p
    rw [oh,ot]
    exact pr
  have firstRun:=Composition.run_join nodeScan outputScan _ _ _ a o ar or'
  have whole:=Composition.run_join (Composition.machine nodeScan outputScan) paddingScan _ _ _
    (joinedReceipt a o) p firstRun pr'
  have tp : (countPaddingRows (n:=q) count).take (bound-(count.val+1))=countPaddingRows (n:=q) count :=
    List.take_of_length_le (by simp only [countPaddingRows,List.length_ofFn];omega)
  have terminal : count.val+2+(bound-(count.val+1))=bound+1:=by have hc:=count.isLt;omega
  have joinedRefs : ro++references bo.nodes.length (countPaddingRows (n:=q) count)=
      refs++references b.nodes.length (RecoveryBoundedGrammar.rows (q:=q) count) := by
    simp only [ro,rn,bo,bn,e,RecoveryBoundedGrammar.rows,RecoveryBoundedGrammar.references_append,
      references,compileExpr_output,compileExpr_length,children_length,Nat.add_assoc,List.append_assoc,
      List.cons_append,List.nil_append]
  refine ⟨joinedReceipt (joinedReceipt a o) p,whole,?_,?_,?_⟩
  · change (a.steps+1+o.steps)+1+p.steps≤forwardBudget B bound count.val
    unfold forwardBudget
    exact Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right as 1) os) 1) ps
  · change p.final.heads=scanHeads
      (heads (graphWord graphPre (children b (RecoveryBoundedGrammar.rows (q:=q) count)))
        (saved stackPre (refs++references b.nodes.length (RecoveryBoundedGrammar.rows (q:=q) count)))) 1 1
    rw [ph]
    simp only [pathConfig,pathState,RowState.configuration,entry,originalState,tp,terminal,
      ←allChildren,joinedRefs]
  · change p.final.tapes=scanData (data (selectedFields (tag 6) q bound (bound+1) C)
      (children b (RecoveryBoundedGrammar.rows (q:=q) count)).nodes.length B P
      (graphWord graphPre (children b (RecoveryBoundedGrammar.rows (q:=q) count)))
      (saved stackPre (refs++references b.nodes.length (RecoveryBoundedGrammar.rows (q:=q) count)))
      (ZeroPadding.pad B (selectedWord (tag 6) q bound (bound+1) C)) source
      (metadata q bound (bound+1) C B extra)) B bound count.val
    rw [pt]
    simp only [pathConfig,pathState,RowState.configuration,entry,originalState,tp,terminal,
      ←allChildren,joinedRefs]

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
