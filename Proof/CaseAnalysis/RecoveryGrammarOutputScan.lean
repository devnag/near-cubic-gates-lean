import Proof.CaseAnalysis.RecoveryGrammarScans

/-! The one original output row sits between the two finite scans.
Its tag-five selection is paid, and its bound-driver advance occurs once. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape Composition SourceInterfaces FinitePredicateCircuit BoundedOracleStructuralCircuit
open RecoveryBoundedNative RecoveryBoundedAddress RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def outputStage:=Composition.machine (reselect (tag 5)) outputBody
noncomputable def outputScan:=TapeEmbedding.machine 1 (RecoveryBoundedGrammarDriver.bump outputStage)
def outputStageBudget (B : ℕ):=atomBudget B+1+rowBodyBudget (paddingBudget B) B
def outputScanBudget (B : ℕ):=outputStageBudget B+2

theorem outputStage_run {q bound G W C D L S B P : ℕ}
    (room : Room W C D L S B P) (alloc : Allocation q bound G W)
    (b : BooleanDAGBuilder (descriptionWidth q bound)) (count : Fin bound)
    (graphPre stackPre source : List Bool) (refs : List ℕ) (extra : Fin 12→List Bool)
    (valid : ValidReferences b refs W)
    (hg : (compileExpr b (outputRowExpr (n:=q) ⟨count.val+1,by omega⟩)).final.nodes.length≤G)
    (graphSupport : ∀ d : BooleanDAGBuilder (descriptionWidth q bound),d.nodes.length≤G → (graphWord graphPre d).length≤S)
    (stackSupport : stackPre.length+W*(2*W+1)≤S) (hs : source.length≤B)
    (width : extra 0=RecoveryBoundedGrammarScalarAdd.unary B (rowWidth q bound)) :
    ∃ r,runFrom outputStage (outputStageBudget B)
      ((originalState (selectedFields (tag 0) q bound (count.val+1) C) b graphPre stackPre
        (ZeroPadding.pad B (selectedWord (tag 0) q bound (count.val+1) C)) refs).configuration outputStage B P source
        (metadata q bound (count.val+1) C B extra))=some r ∧
      r.steps≤outputStageBudget B ∧
      r.final.heads=heads (graphWord graphPre (compileExpr b (outputRowExpr (n:=q) ⟨count.val+1,by omega⟩)).final)
        (saved stackPre (refs++[(compileExpr b (outputRowExpr (n:=q) ⟨count.val+1,by omega⟩)).output.val])) ∧
      r.final.tapes=data (selectedFields (tag 6) q bound (count.val+2) C)
        (compileExpr b (outputRowExpr (n:=q) ⟨count.val+1,by omega⟩)).final.nodes.length B P
        (graphWord graphPre (compileExpr b (outputRowExpr (n:=q) ⟨count.val+1,by omega⟩)).final)
        (saved stackPre (refs++[(compileExpr b (outputRowExpr (n:=q) ⟨count.val+1,by omega⟩)).output.val]))
        (ZeroPadding.pad B (selectedWord (tag 6) q bound (count.val+2) C)) source
        (metadata q bound (count.val+2) C B extra) := by
  let row : Fin (bound+1):=⟨count.val+1,by omega⟩
  obtain ⟨a,ar,as,ah,atapes⟩:=reselect_run room (alloc.scalars row) (tag 0) (tag 5) b.nodes.length
    (graphWord graphPre b) (saved stackPre refs)
    (ZeroPadding.pad B (selectedWord (tag 0) q bound row.val C)) source extra
    (room.pad_packet_length (alloc.scalars row) (tag 0))
  have core:=address_run room alloc b row 5 2 foldRows graphPre stackPre
    (ZeroPadding.pad B (selectedWord (tag 5) q bound row.val C)) source refs extra
    valid hg graphSupport stackSupport hs (room.pad_packet_length (alloc.scalars row) (tag 5))
  obtain ⟨z,zr,zs,zh,zt⟩:=rowBody_run room alloc (addressRow 2 foldRows) (paddingBudget B) b row
    (outputRowExpr (n:=q) row) (tag 5) (tag 6) graphPre stackPre
    (ZeroPadding.pad B (selectedWord (tag 5) q bound row.val C)) source refs extra width core
  have zr' : runFrom outputBody (rowBodyBudget (paddingBudget B) B) (restart a.final outputBody.start)=some z := by
    change runFrom _ _ ⟨_,a.final.heads,a.final.tapes⟩=some z
    rw [ah,atapes]
    exact zr
  have joined:=Composition.run_join (reselect (tag 5)) outputBody _ _ _ a z ar zr'
  refine ⟨joinedReceipt a z,joined,?_,zh,zt⟩
  change a.steps+1+z.steps≤outputStageBudget B
  unfold outputStageBudget
  omega

theorem outputScan_run {q bound G W C D L S B P : ℕ}
    (room : Room W C D L S B P) (alloc : Allocation q bound G W)
    (b : BooleanDAGBuilder (descriptionWidth q bound)) (count : Fin bound)
    (graphPre stackPre source : List Bool) (refs : List ℕ) (extra : Fin 12→List Bool)
    (valid : ValidReferences b refs W)
    (hg : (compileExpr b (outputRowExpr (n:=q) ⟨count.val+1,by omega⟩)).final.nodes.length≤G)
    (graphSupport : ∀ d : BooleanDAGBuilder (descriptionWidth q bound),d.nodes.length≤G → (graphWord graphPre d).length≤S)
    (stackSupport : stackPre.length+W*(2*W+1)≤S) (hs : source.length≤B)
    (width : extra 0=RecoveryBoundedGrammarScalarAdd.unary B (rowWidth q bound)) :
    let before:=originalState (selectedFields (tag 0) q bound (count.val+1) C) b graphPre stackPre
      (ZeroPadding.pad B (selectedWord (tag 0) q bound (count.val+1) C)) refs
    let after:=originalState (selectedFields (tag 6) q bound (count.val+2) C)
      (compileExpr b (outputRowExpr (n:=q) ⟨count.val+1,by omega⟩)).final graphPre stackPre
      (ZeroPadding.pad B (selectedWord (tag 6) q bound (count.val+2) C))
      (refs++[(compileExpr b (outputRowExpr (n:=q) ⟨count.val+1,by omega⟩)).output.val])
    ∃ r,runFrom outputScan (outputScanBudget B)
      ⟨outputScan.start,scanHeads (heads before.out before.stack) (count.val+2) 1,
        scanData (data before.fields before.node B P before.out before.stack before.packet source
          (metadata q bound (count.val+1) C B extra)) B bound count.val⟩=some r ∧
      r.steps≤outputScanBudget B ∧ r.final.heads=scanHeads (heads after.out after.stack) (count.val+3) 1 ∧
      r.final.tapes=scanData (data after.fields after.node B P after.out after.stack after.packet source
        (metadata q bound (count.val+2) C B extra)) B bound count.val := by
  obtain ⟨a,ar,as,ah,atapes⟩:=outputStage_run room alloc b count graphPre stackPre source refs extra
    valid hg graphSupport stackSupport hs width
  obtain ⟨z,zr,zs,zh,zt⟩:=RecoveryBoundedGrammarDriver.bump_run outputStage _ _ (count.val+2)
    (ZeroPadding.pad B (CompareMachine.word (bound+1))) a ar rfl
  have rr:=TapeEmbedding.run_embed (RecoveryBoundedGrammarDriver.bump outputStage)
    (fun _ : Fin 1=>1) (fun _ : Fin 1=>ZeroPadding.pad B (CompareMachine.word (count.val+1))) _ _ z zr
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 1=>1)
    (fun _ : Fin 1=>ZeroPadding.pad B (CompareMachine.word (count.val+1))) z,rr,?_,?_,?_⟩
  · change z.steps≤outputScanBudget B
    unfold outputScanBudget
    omega
  · change RecoveryBoundedGrammarDriver.heads z.final.heads 1=_
    rw [zh,ah]
    rfl
  · change RecoveryBoundedGrammarDriver.data z.final.tapes _=_
    rw [zt,atapes]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
