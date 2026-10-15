import Proof.CaseAnalysis.RecoveryFixedRows

/-! Preserve the grammar's actual paid stack backing through every row and
the fixed-count conjunction. Zero-padding transports the same machine. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedFixedRows
open LocalBitMultitape Composition SourceInterfaces RepairSource CanonicalRecoveryLanguage
open RepairSource.ProjectionNormalization BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedRows
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def stackCapacity (P : ℕ) (i : Fin 116):=if i=74 then P else 0
def stackPadded (P : ℕ) (A : Fin 116→List Bool) (i : Fin 116):=ZeroPadding.pad (stackCapacity P i) (A i)

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n} {count : Fin bound} {hc : count.val+1≤bound}

theorem padded_run (z : Resources p R Q hr hq x (count.val+1) hc)
    (P : ℕ) (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool)
    (hFinal : (compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count).final.nodes.length≤z.G) :
    let grammar:=compileExpr b (fixedCountGrammarExpr (n:=R) count)
    let original:=compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count
    ∃ f : Forward z grammar.final (allRandomness R), ∃ r,
      runFrom machine (budget z.B z.W R)
        ⟨machine.start,startHeads (z.heads grammar.final (RecoveryBoundedClauseCollect.pushed grammar.output.val stack)),
          stackPadded P (scanData (z.bank grammar.final 0 (RecoveryBoundedClauseCollect.pushed grammar.output.val stack)) (2^R))⟩=some r ∧
      r.steps≤budget z.B z.W R ∧ r.final.heads=(result z f.next f.refs grammar.output.val stack).heads ∧
      r.final.tapes=stackPadded P (result z f.next f.refs grammar.output.val stack).tapes ∧
      r.final.tapes 20=z.word original.final ∧ r.final.tapes 25=List.replicate original.output.val true := by
  obtain ⟨f,base,br,bs,bh,bt,bg,bo⟩:=run z b stack hFinal
  obtain ⟨r,rr,rf,rs,_⟩:=ZeroPadding.run_config machine (stackCapacity P) _ _ base br
  refine ⟨f,r,rr,rs.le.trans bs,?_,?_,?_,?_⟩
  · rw [rf]
    exact bh
  · rw [rf]
    change stackPadded P base.final.tapes=_
    rw [bt]
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 20)=_
    rw [ZeroPadding.pad_zero,bg]
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 25)=_
    rw [ZeroPadding.pad_zero,bo]

end NearCubicWires.RepairOrdinary.RecoveryBoundedFixedRows
