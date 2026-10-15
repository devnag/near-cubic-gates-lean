import Proof.CaseAnalysis.RecoveryRowsFoldRun

/-! Exact original graph, output and cursor at the end of the row fold. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowsFold
open LocalBitMultitape SourceInterfaces RecoveryBoundedRows RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (node C D F L B n count Q clauses : ℕ) (out source pre packet : List Bool)
variable (refs : List ℕ) (P : Fin 37→List Bool)

theorem result_slot (j : Fin 35) :
    (result node C D F L B n count Q clauses out source pre packet refs P).tapes (slots j)=
      ZeroPadding.pad (caps B j) ((RecoveryBoundedGrammarFold.finalConfiguration true node C out pre refs).tapes j) := by
  simp only [result,RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,ZeroPadding.config]

theorem head_slot (j : Fin 35) :
    (result node C D F L B n count Q clauses out source pre packet refs P).heads (slots j)=
      (RecoveryBoundedGrammarFold.finalConfiguration true node C out pre refs).heads j := by
  simp only [result,RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,ZeroPadding.config]

theorem result_graph (arity : ℕ) :
    (result node C D F L B n count Q clauses out source pre packet refs P).tapes 20=
      out++(allSuffix (n:=arity) node refs).flatMap PCPPRequestNodeSchema.native := by
  have h:=result_slot node C D F L B n count Q clauses out source pre packet refs P 20
  change (result node C D F L B n count Q clauses out source pre packet refs P).tapes 20=
    ZeroPadding.pad 0 ((RecoveryBoundedGrammarFold.finalConfiguration true node C out pre refs).tapes 20) at h
  rw [ZeroPadding.pad_zero,RecoveryBoundedGrammarFold.output_graph arity,←allSuffix_reverse] at h
  exact h

theorem result_output :
    (result node C D F L B n count Q clauses out source pre packet refs P).tapes 25=
      List.replicate (node+refs.length) true := by
  have h:=result_slot node C D F L B n count Q clauses out source pre packet refs P 25
  change (result node C D F L B n count Q clauses out source pre packet refs P).tapes 25=
    ZeroPadding.pad 0 ((RecoveryBoundedGrammarFold.finalConfiguration true node C out pre refs).tapes 25) at h
  rw [ZeroPadding.pad_zero,RecoveryBoundedGrammarFold.output_counter] at h
  exact h

theorem graph_head :
    (result node C D F L B n count Q clauses out source pre packet refs P).heads 20=
      ((result node C D F L B n count Q clauses out source pre packet refs P).tapes 20).length := by
  have h:=head_slot node C D F L B n count Q clauses out source pre packet refs P 20
  have t:=result_slot node C D F L B n count Q clauses out source pre packet refs P 20
  change (result node C D F L B n count Q clauses out source pre packet refs P).heads 20=_ at h
  change (result node C D F L B n count Q clauses out source pre packet refs P).tapes 20=
    ZeroPadding.pad 0 ((RecoveryBoundedGrammarFold.finalConfiguration true node C out pre refs).tapes 20) at t
  rw [h,t,ZeroPadding.pad_zero]
  rfl

theorem stack_head :
    (result node C D F L B n count Q clauses out source pre packet refs P).heads 74=pre.length := by
  have h:=head_slot node C D F L B n count Q clauses out source pre packet refs P 31
  change (result node C D F L B n count Q clauses out source pre packet refs P).heads 74=_ at h
  rw [h]
  change (RecoveryBoundedNativeFoldLoop.stack pre []).length=pre.length
  simp only [RecoveryBoundedNativeFoldLoop.stack,List.reverse_nil,RecoveryBoundedNativeUnaryLoop.stackWords,
    List.flatMap_nil,List.append_nil]

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowsFold
