import Proof.CaseAnalysis.RecoveryCountConjunctionStep

/-! The one original fixed-count AND executes directly on the retained
116-tape row bank, including the erased stack tail and the same driver. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountConjunction
open LocalBitMultitape SourceInterfaces RecoveryBoundedNativeFoldLoop
open RecoveryBoundedRowsFold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def state (node : ℕ) (out : List Bool) (refs : List ℕ):=
  State.iterate true refs.reverse ⟨node,0,0,out++RecoveryBoundedGrammarFold.bits true⟩
noncomputable def machine:=Focus.machine localMachine

variable (node C D F L B n count Q clauses ref : ℕ) (out source pre packet : List Bool)
variable (refs : List ℕ) (P : Fin 37→List Bool)

noncomputable def input:=RecoveryBoundedRowsFold.result node C D F L B n count Q clauses out source
  (RecoveryBoundedClauseCollect.pushed ref pre) packet refs P
noncomputable def result:=RecoveryFocus.config slots
  (input node C D F L B n count Q clauses ref out source pre packet refs P).heads
  (input node C D F L B n count Q clauses ref out source pre packet refs P).tapes
  (ZeroPadding.config (caps B) (after C refs.length ref pre (state node out refs)))

theorem input_heads (j : Fin 35) :
    (input node C D F L B n count Q clauses ref out source pre packet refs P).heads (slots j)=
      (before C refs.length ref pre (state node out refs)).heads j :=
  RecoveryBoundedRowsFold.head_slot node C D F L B n count Q clauses out source
    (RecoveryBoundedClauseCollect.pushed ref pre) packet refs P j

theorem input_tapes (j : Fin 35) :
    (input node C D F L B n count Q clauses ref out source pre packet refs P).tapes (slots j)=
      ZeroPadding.pad (caps B j) ((before C refs.length ref pre (state node out refs)).tapes j) :=
  RecoveryBoundedRowsFold.result_slot node C D F L B n count Q clauses out source
    (RecoveryBoundedClauseCollect.pushed ref pre) packet refs P j

theorem run (W : ℕ) (hr : ref≤W) (ha : node+refs.length≤W) (hC : 16384*(W+1)^2≤C) :
    ∃ r,runFrom machine (24*C+64)
      ⟨machine.start,(input node C D F L B n count Q clauses ref out source pre packet refs P).heads,
        (input node C D F L B n count Q clauses ref out source pre packet refs P).tapes⟩=some r ∧
      r.steps≤24*C+64 ∧
      r.final.heads=(result node C D F L B n count Q clauses ref out source pre packet refs P).heads ∧
      r.final.tapes=(result node C D F L B n count Q clauses ref out source pre packet refs P).tapes := by
  have ha' : (state node out refs).acc≤W := by
    have h:=iterate_meaning (n:=0) true refs.reverse ⟨node,0,0,out++RecoveryBoundedGrammarFold.bits true⟩
    simpa only [state,h.1,List.length_reverse] using ha
  obtain ⟨base,br,bs,bh,bt⟩:=local_run C W refs.length ref pre (state node out refs) hr ha' hC
  obtain ⟨r,rr,rs,rh,rt⟩:=Focus.run localMachine (24*C+64) B
    ⟨localMachine.start,(before C refs.length ref pre (state node out refs)).heads,
      (before C refs.length ref pre (state node out refs)).tapes⟩
    (input node C D F L B n count Q clauses ref out source pre packet refs P).heads
    (input node C D F L B n count Q clauses ref out source pre packet refs P).tapes base br
    (input_heads node C D F L B n count Q clauses ref out source pre packet refs P)
    (input_tapes node C D F L B n count Q clauses ref out source pre packet refs P)
  refine ⟨r,rr,rs.le.trans bs,?_,?_⟩
  · rw [rh]
    simp only [result,RecoveryFocus.config,ZeroPadding.config,bh]
  · rw [rt]
    simp only [result,RecoveryFocus.config,ZeroPadding.config,bt]

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountConjunction
