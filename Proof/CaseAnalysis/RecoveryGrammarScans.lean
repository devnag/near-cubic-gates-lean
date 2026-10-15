import Proof.CaseAnalysis.RecoveryGrammarRowPath

/-! The original node and padding scans consume two paid finite drivers.
Each node advances the retained bound driver; padding starts at its exact suffix. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape SourceInterfaces FinitePredicateCircuit BoundedOracleStructuralCircuit
open RecoveryBoundedNative RecoveryBoundedAddress RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def nodeScan:=RecoveryBoundedGrammarRepeat.machine (RecoveryBoundedGrammarDriver.bump nodeBody)
noncomputable def paddingScan:=TapeEmbedding.machine 1 (RecoveryBoundedGrammarRepeat.machine paddingBody)
def nodeScanBudget (B count : ℕ):=(count+1)*((rowBodyBudget (nodeBudget B) B+2)+2)+(count+1)+3
def paddingScanBudget (B bound count : ℕ):=(bound-(count+1))*(rowBodyBudget (paddingBudget B) B+2)+(bound+1)+3

def scanHeads (H : Fin 112→ℕ) (boundPos countPos : ℕ):=
  RecoveryBoundedGrammarDriver.heads (RecoveryBoundedGrammarDriver.heads H boundPos) countPos
def scanData (A : Fin 112→List Bool) (B bound count : ℕ):=
  RecoveryBoundedGrammarDriver.data (RecoveryBoundedGrammarDriver.data A
    (ZeroPadding.pad B (CompareMachine.word (bound+1)))) (ZeroPadding.pad B (CompareMachine.word (count+1)))

noncomputable def nodeScanState {q bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth q bound)) (count : Fin bound)
    (C B P : ℕ) (graphPre stackPre source : List Bool) (refs : List ℕ) (extra : Fin 12→List Bool) (i : ℕ) :=
  let c:=pathConfig nodeBody b (countNodeRows count) (tag 0) 0 C B P graphPre stackPre source refs extra i
  (⟨(RecoveryBoundedGrammarDriver.bump nodeBody).start,
    RecoveryBoundedGrammarDriver.heads c.heads (i+1),
    RecoveryBoundedGrammarDriver.data c.tapes (ZeroPadding.pad B (CompareMachine.word (bound+1)))⟩ : Configuration 113 _)

theorem nodeScan_run {q bound G W C D L S B P : ℕ}
    (room : Room W C D L S B P) (alloc : Allocation q bound G W)
    (b : BooleanDAGBuilder (descriptionWidth q bound)) (count : Fin bound)
    (graphPre stackPre source : List Bool) (refs : List ℕ) (extra : Fin 12→List Bool)
    (valid : ValidReferences b refs W) (hg : (children b (countNodeRows count)).nodes.length≤G)
    (graphSupport : ∀ d : BooleanDAGBuilder (descriptionWidth q bound),d.nodes.length≤G → (graphWord graphPre d).length≤S)
    (stackSupport : stackPre.length+W*(2*W+1)≤S) (hs : source.length≤B)
    (width : extra 0=RecoveryBoundedGrammarScalarAdd.unary B (rowWidth q bound)) :
    ∃ r,runFrom nodeScan (nodeScanBudget B count.val)
      ⟨nodeScan.start,scanHeads (pathConfig nodeBody b (countNodeRows count) (tag 0) 0 C B P graphPre stackPre source refs extra 0).heads 1 1,
        scanData (pathConfig nodeBody b (countNodeRows count) (tag 0) 0 C B P graphPre stackPre source refs extra 0).tapes B bound count.val⟩=some r ∧
      r.steps≤nodeScanBudget B count.val ∧
      r.final.heads=scanHeads (pathConfig nodeBody b (countNodeRows count) (tag 0) 0 C B P graphPre stackPre source refs extra (count.val+1)).heads (count.val+2) 1 ∧
      r.final.tapes=scanData (pathConfig nodeBody b (countNodeRows count) (tag 0) 0 C B P graphPre stackPre source refs extra (count.val+1)).tapes B bound count.val := by
  have supplier : ∀ i,0 ≤ i → i < 0+(count.val+1) →
      ∃ r,runFrom (RecoveryBoundedGrammarDriver.bump nodeBody) (rowBodyBudget (nodeBudget B) B+2)
        (nodeScanState b count C B P graphPre stackPre source refs extra i)=some r ∧
        r.steps≤rowBodyBudget (nodeBudget B) B+2 ∧
        r.final.heads=(nodeScanState b count C B P graphPre stackPre source refs extra (i+1)).heads ∧
        r.final.tapes=(nodeScanState b count C B P graphPre stackPre source refs extra (i+1)).tapes := by
    intro i _ hi
    obtain ⟨a,ar,as,ah,atapes⟩:=node_path_run room alloc b count graphPre stackPre source refs extra
      valid hg graphSupport stackSupport hs width i (by omega)
    obtain ⟨r,rr,rs,rh,rt⟩:=RecoveryBoundedGrammarDriver.bump_run nodeBody _ _ (i+1)
      (ZeroPadding.pad B (CompareMachine.word (bound+1))) a ar rfl
    refine ⟨r,rr,by omega,?_,?_⟩
    · simpa only [nodeScanState,ah] using rh
    · simpa only [nodeScanState,atapes] using rt
  obtain ⟨r,rr,rs,rh,rt⟩:=RecoveryBoundedGrammarRepeat.padded_run (RecoveryBoundedGrammarDriver.bump nodeBody)
    (nodeScanState b count C B P graphPre stackPre source refs extra) (rowBodyBudget (nodeBudget B) B+2)
    (count.val+1) (count.val+1) 0 0 B (by omega) (by intro i _ _;rfl) supplier
  refine ⟨r,rr,rs,?_,?_⟩
  · simpa only [nodeScanState,Nat.zero_add,Nat.add_assoc,scanHeads] using rh
  · simpa only [nodeScanState,Nat.zero_add,scanData] using rt

theorem paddingScan_run {q bound G W C D L S B P : ℕ}
    (room : Room W C D L S B P) (alloc : Allocation q bound G W)
    (b : BooleanDAGBuilder (descriptionWidth q bound)) (count : Fin bound)
    (graphPre stackPre source : List Bool) (refs : List ℕ) (extra : Fin 12→List Bool)
    (valid : ValidReferences b refs W) (hg : (children b (countPaddingRows count)).nodes.length≤G)
    (graphSupport : ∀ d : BooleanDAGBuilder (descriptionWidth q bound),d.nodes.length≤G → (graphWord graphPre d).length≤S)
    (stackSupport : stackPre.length+W*(2*W+1)≤S) (hs : source.length≤B)
    (width : extra 0=RecoveryBoundedGrammarScalarAdd.unary B (rowWidth q bound)) :
    ∃ r,runFrom paddingScan (paddingScanBudget B bound count.val)
      ⟨paddingScan.start,scanHeads (pathConfig paddingBody b (countPaddingRows count) (tag 6) (count.val+2) C B P graphPre stackPre source refs extra 0).heads (count.val+3) 1,
        scanData (pathConfig paddingBody b (countPaddingRows count) (tag 6) (count.val+2) C B P graphPre stackPre source refs extra 0).tapes B bound count.val⟩=some r ∧
      r.steps≤paddingScanBudget B bound count.val ∧
      r.final.heads=scanHeads (pathConfig paddingBody b (countPaddingRows count) (tag 6) (count.val+2) C B P graphPre stackPre source refs extra (bound-(count.val+1))).heads 1 1 ∧
      r.final.tapes=scanData (pathConfig paddingBody b (countPaddingRows count) (tag 6) (count.val+2) C B P graphPre stackPre source refs extra (bound-(count.val+1))).tapes B bound count.val := by
  obtain ⟨a,ar,as,ah,atapes⟩:=RecoveryBoundedGrammarRepeat.padded_run paddingBody
    (pathConfig paddingBody b (countPaddingRows count) (tag 6) (count.val+2) C B P graphPre stackPre source refs extra)
    (rowBodyBudget (paddingBudget B) B) (bound-(count.val+1)) (bound+1) (count.val+2) 0 B
    (by have hc:=count.isLt;omega) (by intro i _ _;rfl)
    (by intro i _ hi;exact padding_path_run room alloc b count graphPre stackPre source refs extra
          valid hg graphSupport stackSupport hs width i (by omega))
  have nextPos : count.val+2+1=count.val+3:=by omega
  rw [nextPos] at ar
  rw [Nat.zero_add] at ah atapes
  have rr:=TapeEmbedding.run_embed (RecoveryBoundedGrammarRepeat.machine paddingBody)
    (fun _ : Fin 1=>1) (fun _ : Fin 1=>ZeroPadding.pad B (CompareMachine.word (count.val+1))) _ _ a ar
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 1=>1)
    (fun _ : Fin 1=>ZeroPadding.pad B (CompareMachine.word (count.val+1))) a,rr,as,?_,?_⟩
  · change RecoveryBoundedGrammarDriver.heads a.final.heads 1=_
    rw [ah]
    rfl
  · change RecoveryBoundedGrammarDriver.data a.final.tapes _=_
    rw [atapes]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
