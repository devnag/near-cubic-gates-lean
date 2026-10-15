import Proof.CaseAnalysis.RecoveryGrammarForward

/-! The complete original fixed-count grammar runs on its physically ready
scalar/driver bank. It returns the exact graph, actual incremented count and
one saved output reference used by the following original verifier rows. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape Composition SourceInterfaces FinitePredicateCircuit BoundedOracleStructuralCircuit
open RecoveryBoundedNative RecoveryBoundedAddress RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def compiled:=Composition.machine forward finishScan
def compiledBudget (B bound count : ℕ):=forwardBudget B bound count+1+finishScanBudget B

theorem compiled_run {q bound G W C D L S B P : ℕ}
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
    let after:=originalState (selectedFields foldRows q bound (bound+1) C)
      (compileExpr b (fixedCountGrammarExpr (n:=q) count)).final graphPre stackPre
      (ZeroPadding.pad B (selectedWord foldRows q bound (bound+1) C))
      (refs++[(compileExpr b (fixedCountGrammarExpr (n:=q) count)).output.val])
    ∃ r,runFrom compiled (compiledBudget B bound count.val)
      ⟨compiled.start,scanHeads (heads before.out before.stack) 1 1,
        scanData (data before.fields before.node B P before.out before.stack before.packet source
          (metadata q bound 0 C B extra)) B bound count.val⟩=some r ∧
      r.steps≤compiledBudget B bound count.val ∧ r.final.heads=scanHeads (heads after.out after.stack) 1 1 ∧
      r.final.tapes=scanData (data after.fields after.node B P after.out after.stack after.packet source
        (metadata q bound (bound+1) C B extra)) B bound count.val := by
  obtain ⟨a,ar,as,ah,atapes⟩:=forward_run room alloc b count graphPre stackPre source refs extra
    valid hg graphSupport stackSupport hs width
  have scalars:=(alloc.next_scalars (⟨bound,by omega⟩ : Fin (bound+1))).2.2
  obtain ⟨z,zr,zs,zh,zt⟩:=finishStage_run room scalars b count graphPre stackPre source refs extra
    valid hg alloc.graph graphSupport stackSupport hs
  let H:=fun _ : Fin 1=>1
  let boundWord:=fun _ : Fin 1=>ZeroPadding.pad B (CompareMachine.word (bound+1))
  let countWord:=fun _ : Fin 1=>ZeroPadding.pad B (CompareMachine.word (count.val+1))
  let z1:=TapeEmbedding.receipt H boundWord z
  let z2:=TapeEmbedding.receipt H countWord z1
  have er1:=TapeEmbedding.run_embed finishStage H boundWord _ _ z zr
  have er2:=TapeEmbedding.run_embed (TapeEmbedding.machine 1 finishStage) H countWord _ _ z1 er1
  have joinRun : runFrom finishScan (finishScanBudget B) (restart a.final finishScan.start)=some z2 := by
    change runFrom _ _ ⟨_,a.final.heads,a.final.tapes⟩=some z2
    rw [ah,atapes]
    exact er2
  have joined:=Composition.run_join forward finishScan _ _ _ a z2 ar joinRun
  refine ⟨joinedReceipt a z2,joined,?_,?_,?_⟩
  · change a.steps+1+z.steps≤compiledBudget B bound count.val
    exact Nat.add_le_add (Nat.add_le_add_right as 1) zs
  · change scanHeads z.final.heads 1 1=_
    rw [zh]
  · change scanData z.final.tapes B bound count.val=_
    rw [zt]

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
