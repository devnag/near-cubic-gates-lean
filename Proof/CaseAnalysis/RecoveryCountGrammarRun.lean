import Proof.CaseAnalysis.RecoveryCountRowsDock

/-! The literal original fixed-count grammar on the enclosing count bank.
Its single saved output feeds the already checked original verifier rows. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountGrammarBank
open LocalBitMultitape SourceInterfaces FinitePredicateCircuit BoundedOracleStructuralCircuit
open RecoveryBoundedCountBank
open RecoveryBoundedGrammarCold (Room Allocation graphWord selectedFields selectedWord tag foldRows metadata)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem saved_nil (stack : List Bool) : RecoveryBoundedGrammarCold.saved stack []=stack := by
  simp only [RecoveryBoundedGrammarCold.saved,RecoveryBoundedNativeUnaryLoop.stackWords,
    List.flatMap_nil,List.append_nil]
theorem saved_single (stack : List Bool) (ref : ℕ) :
    RecoveryBoundedGrammarCold.saved stack [ref]=RecoveryBoundedAddress.pushed ref stack := by
  simp only [RecoveryBoundedGrammarCold.saved,RecoveryBoundedNativeUnaryLoop.stackWords,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,RecoveryBoundedAddress.pushed]

noncomputable def compiled:=RecoveryFocus.machine grammarSlots RecoveryBoundedGrammarCold.compiled

theorem compiled_run {q bound G W C D L S B P : ℕ}
    (room : Room W C D L S B P) (alloc : Allocation q bound G W)
    (b : BooleanDAGBuilder (descriptionWidth q bound)) (count : Fin bound)
    (graphPre stack source : List Bool) (proj : Fin 37→List Bool) (total : ℕ) (extra : Fin 12→List Bool)
    (hg : (compileExpr b (fixedCountGrammarExpr (n:=q) count)).final.nodes.length≤G)
    (graphSupport : ∀ d : BooleanDAGBuilder (descriptionWidth q bound),d.nodes.length≤G → (graphWord graphPre d).length≤S)
    (stackSupport : stack.length+W*(2*W+1)≤S) (hs : source.length≤B)
    (width : extra 0=RecoveryBoundedGrammarScalarAdd.unary B (rowWidth q bound)) :
    let original:=compileExpr b (fixedCountGrammarExpr (n:=q) count)
    let saved:=RecoveryBoundedAddress.pushed original.output.val stack
    ∃ r,runFrom compiled (RecoveryBoundedGrammarCold.compiledBudget B bound count.val)
      ⟨compiled.start,heads (graphWord graphPre b) stack 1 1,
        data B P (RecoveryBoundedGrammarBank.ready (selectedFields (tag 0) q bound 0 C)
          b.nodes.length B (graphWord graphPre b) stack (ZeroPadding.pad B (selectedWord (tag 0) q bound 0 C)) source)
          proj total (metadata q bound 0 C B extra)
          (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (bound+1)))
          (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (count.val+1)))⟩=some r ∧
      r.steps≤RecoveryBoundedGrammarCold.compiledBudget B bound count.val ∧
      r.final.heads=heads (graphWord graphPre original.final) saved 1 1 ∧
      r.final.tapes=data B P (RecoveryBoundedGrammarBank.ready (selectedFields foldRows q bound (bound+1) C)
        original.final.nodes.length B (graphWord graphPre original.final) saved
        (ZeroPadding.pad B (selectedWord foldRows q bound (bound+1) C)) source)
        proj total (metadata q bound (bound+1) C B extra)
        (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (bound+1)))
        (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (count.val+1))) := by
  dsimp only
  obtain ⟨a,ar,as,ah,atapes⟩:=RecoveryBoundedGrammarCold.compiled_run room alloc b count graphPre stack source [] extra
    ⟨Nat.zero_le _,by simp⟩ hg graphSupport stackSupport hs width
  simp only [RecoveryBoundedGrammarCold.originalState,List.nil_append,saved_nil,saved_single] at ar ah atapes
  exact focus_run RecoveryBoundedGrammarCold.compiled _ B P total _ _ bound count.val _ _
    _ _ _ _ _ _ source proj _ _ a ar as ah atapes

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountGrammarBank
