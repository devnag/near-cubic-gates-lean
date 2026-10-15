import Proof.CaseAnalysis.RecoveryRowsRun

/-! The whole original randomness list, using one physically retained
Compare(2^R) driver for the forward rows and the original reverse ANDs. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRows
open LocalBitMultitape Composition SourceInterfaces RepairSource CanonicalRecoveryLanguage
open RepairSource.ProjectionNormalization BoundedOracleStructuralCircuit FinitePredicateCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n} {count : ℕ} {hc : count≤bound}

theorem all_run (z : Resources p R Q hr hq x count hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool)
    (hFinal : (compileVerifierRows (compactProjectionPCP (p.normalized R Q hr hq)) x count hc b
      (allRandomness R)).final.nodes.length≤z.G) :
    let original:=compileVerifierRows (compactProjectionPCP (p.normalized R Q hr hq)) x count hc b (allRandomness R)
    ∃ f : Forward z b (allRandomness R), ∃ r,
      runFrom machine (budget z.B z.W (2^R-1))
        ⟨machine.start,startHeads (z.heads b stack),scanData (z.bank b 0 stack) (2^R)⟩=some r ∧
      r.steps≤budget z.B z.W (2^R-1) ∧
      r.final.heads=(foldResult z f.next f.refs (2^R-1) stack).heads ∧
      r.final.tapes=(foldResult z f.next f.refs (2^R-1) stack).tapes ∧
      r.final.tapes 20=z.word original.final ∧
      r.final.tapes 25=List.replicate original.output.val true := by
  have hp : 0<2^R:=Nat.two_pow_pos R
  have he : 2^R-1+1=2^R:=by omega
  have hrows : randomnesses R 0 (2^R-1+1)=allRandomness R:=by rw [he,randomnesses_all]
  have hf : (compileVerifierRows (compactProjectionPCP (p.normalized R Q hr hq)) x count hc b
      (randomnesses R 0 (2^R-1+1))).final.nodes.length≤z.G := by
    rw [hrows]
    exact hFinal
  have result:=run z b (2^R-1) stack (by omega) hf
  rw [hrows] at result
  simpa only [he] using result

end NearCubicWires.RepairOrdinary.RecoveryBoundedRows
