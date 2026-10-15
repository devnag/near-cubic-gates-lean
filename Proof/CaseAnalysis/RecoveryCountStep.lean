import Proof.CaseAnalysis.RecoveryCountBudget

/-! The checked whole fixed-count worker advances the one literal uniform
bank. This is the sole supplier consumed by the original finite count loop. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountUniform
open LocalBitMultitape SourceInterfaces RepairSource CanonicalRecoveryLanguage
open RepairSource.ProjectionNormalization BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem endpoint {t s : ℕ} (worker : Machine t s) (small large : ℕ)
    (H H' : Fin t→ℕ) (A A' A'' : Fin t→List Bool)
    (h : ∃ r,runFrom worker small ⟨worker.start,H,A⟩=some r ∧ r.steps ≤ small ∧
      r.final.heads=H' ∧ r.final.tapes=A') (hb : small ≤ large) (ha : A'=A'') :
    ∃ r,runFrom worker large ⟨worker.start,H,A⟩=some r ∧ r.steps ≤ large ∧
      r.final.heads=H' ∧ r.final.tapes=A'' := by
  obtain ⟨r,rr,rs,rh,rt⟩:=h
  have more:=runFrom_moreFuel worker small (large-small) _ r rr
  rw [Nat.add_sub_of_le hb] at more
  exact ⟨r,more,rs.trans hb,rh,rt.trans ha⟩

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n}

theorem Resources.body_run (z : Resources p R Q hr hq (bound:=bound) x)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (count : Fin bound)
    (stack : List Bool) (extra : Fin 12→List Bool)
    (rawWidth : extra 0=RecoveryBoundedGrammarScalarAdd.unary z.base.B (rowWidth R bound))
    (rawQ : extra 3=RecoveryBoundedGrammarScalarAdd.unary z.base.B Q)
    (rawClauses : extra 4=RecoveryBoundedGrammarScalarAdd.unary z.base.B (Codec.clauses p).length)
    (rawR : extra 5=RecoveryBoundedGrammarScalarAdd.unary z.base.B (R+1))
    (hStack : stack.length+z.base.W*(2*z.base.W+1)≤z.base.S)
    (hFinal : (compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count).final.nodes.length≤z.base.G)
    (hP : stack.length+(2^R+1)*(2*z.base.W+1)≤z.P) :
    let original:=compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count
    let saved:=RecoveryBoundedAddress.pushed original.output.val stack
    ∃ r,runFrom RecoveryBoundedCountPipeline.machine (bodyBudget z.base.B z.base.W R)
      ⟨RecoveryBoundedCountPipeline.machine.start,z.heads b stack,z.bank b count.val stack extra⟩=some r ∧
      r.steps≤bodyBudget z.base.B z.base.W R ∧ r.final.heads=z.heads original.final saved ∧
      r.final.tapes=z.bank original.final (count.val+1) saved extra := by
  dsimp only
  have hcount : count.val+1≤bound:=by omega
  let a:=z.atCount (count.val+1) hcount
  have width : extraAt z.base.B count.val extra 0=RecoveryBoundedGrammarScalarAdd.unary z.base.B (rowWidth R bound) := by
    simpa only [extraAt,Function.update_of_ne (by decide : (0 : Fin 12)≠1)] using rawWidth
  have qraw : extraAt z.base.B count.val extra 3=RecoveryBoundedGrammarScalarAdd.unary z.base.B Q := by
    simpa only [extraAt,Function.update_of_ne (by decide : (3 : Fin 12)≠1)] using rawQ
  have clraw : extraAt z.base.B count.val extra 4=RecoveryBoundedGrammarScalarAdd.unary z.base.B (Codec.clauses p).length := by
    simpa only [extraAt,Function.update_of_ne (by decide : (4 : Fin 12)≠1)] using rawClauses
  have rraw : extraAt z.base.B count.val extra 5=RecoveryBoundedGrammarScalarAdd.unary z.base.B (R+1) := by
    simpa only [extraAt,Function.update_of_ne (by decide : (5 : Fin 12)≠1)] using rawR
  have htail : a.packetTail=List.replicate (z.base.B-(RecoveryBoundedRowReload.word
      (RecoveryBoundedRowPrototype.fields (capacity z.base.W) z.base.D
        (OuterPCPRecovery.boundedCircuitFieldLimit R bound) z.base.L R (count.val+1) Q (Codec.clauses p).length)).length) false := by
    simp only [a,Resources.atCount,Resources.fields]
  have hW : a.W=z.base.W:=rfl
  have hG : a.G=z.base.G:=rfl
  have hD : a.D=z.base.D:=rfl
  have hL : a.L=z.base.L:=rfl
  have hB : a.B=z.base.B:=rfl
  have hS : a.S=z.base.S:=rfl
  have hsource : a.sourceTail=z.base.sourceTail:=rfl
  have hword (g : BooleanDAGBuilder (descriptionWidth R bound)) : a.word g=z.base.word g:=rfl
  have old:=RecoveryBoundedCountPipeline.run
    (p:=p) (R:=R) (Q:=Q) (hr:=hr) (hq:=hq) (n:=n) (bound:=bound) (x:=x) (count:=count) (hc:=hcount)
    a z.P
  simp only [hW,hG,hD,hL,hB,hS,hsource,hword] at old
  have run:=old z.room z.allocation b stack (z.currentPacket count.val) (z.currentFields count.val)
    (extraAt z.base.B count.val extra) z.clauses_bound width (by simp only [extraAt,Function.update_self])
    qraw clraw rraw htail (z.current_fields_bound count.val (by omega))
    (z.current_packet_bound count.val (by omega)) z.source_bound hStack hFinal hP
  exact endpoint RecoveryBoundedCountPipeline.machine _ _ _ _ _ _ _ run (z.body_budget count)
    (z.next_bank count.val hcount _ _ extra)

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountUniform
