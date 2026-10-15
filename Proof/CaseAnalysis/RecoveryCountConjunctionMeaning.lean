import Proof.CaseAnalysis.RecoveryCountMeaning

/-! The retained one-node conjunction has the literal original output,
graph append cursor and erased stack; the output is still a reference. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountConjunction
open LocalBitMultitape SourceInterfaces RecoveryBoundedNativeFoldLoop RecoveryBoundedRowsFold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (node C D F L B n count Q clauses ref : ℕ) (out source pre packet : List Bool)
variable (refs : List ℕ) (P : Fin 37→List Bool)

theorem result_slot (j : Fin 35) :
    (result node C D F L B n count Q clauses ref out source pre packet refs P).tapes (slots j)=
      ZeroPadding.pad (caps B j) ((after C refs.length ref pre (state node out refs)).tapes j) := by
  simp only [result,RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,ZeroPadding.config]

theorem head_slot (j : Fin 35) :
    (result node C D F L B n count Q clauses ref out source pre packet refs P).heads (slots j)=
      (after C refs.length ref pre (state node out refs)).heads j := by
  simp only [result,RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,ZeroPadding.config]

theorem input_graph :
    (input node C D F L B n count Q clauses ref out source pre packet refs P).tapes 20=(state node out refs).out := by
  have h:=input_tapes node C D F L B n count Q clauses ref out source pre packet refs P 20
  change (input node C D F L B n count Q clauses ref out source pre packet refs P).tapes 20=
    ZeroPadding.pad 0 (state node out refs).out at h
  simpa only [ZeroPadding.pad_zero] using h

theorem state_acc : (state node out refs).acc=node+refs.length := by
  have h:=iterate_meaning (n:=0) true refs.reverse ⟨node,0,0,out++RecoveryBoundedGrammarFold.bits true⟩
  simpa only [state,List.length_reverse] using h.1

theorem result_graph (arity : ℕ) :
    (result node C D F L B n count Q clauses ref out source pre packet refs P).tapes 20=
      (input node C D F L B n count Q clauses ref out source pre packet refs P).tapes 20++
        PCPPRequestNodeSchema.native (.and ref (node+refs.length) : BooleanNode arity) := by
  have h:=result_slot node C D F L B n count Q clauses ref out source pre packet refs P 20
  change (result node C D F L B n count Q clauses ref out source pre packet refs P).tapes 20=
    ZeroPadding.pad 0 ((state node out refs).out++RecoveryBoundedNativeFold.emitted true ref (state node out refs).acc) at h
  rw [ZeroPadding.pad_zero,state_acc] at h
  rw [input_graph]
  exact h

theorem result_output :
    (result node C D F L B n count Q clauses ref out source pre packet refs P).tapes 25=
      List.replicate (node+refs.length+1) true := by
  have h:=result_slot node C D F L B n count Q clauses ref out source pre packet refs P 25
  change (result node C D F L B n count Q clauses ref out source pre packet refs P).tapes 25=
    ZeroPadding.pad 0 (List.replicate ((state node out refs).acc+1) true) at h
  simpa only [ZeroPadding.pad_zero,state_acc] using h

theorem stack_head :
    (result node C D F L B n count Q clauses ref out source pre packet refs P).heads 74=pre.length := by
  have h:=head_slot node C D F L B n count Q clauses ref out source pre packet refs P 31
  change (result node C D F L B n count Q clauses ref out source pre packet refs P).heads 74=
    (stack pre []).length at h
  simpa only [stack,List.reverse_nil,RecoveryBoundedNativeUnaryLoop.stackWords,List.flatMap_nil,List.append_nil] using h

theorem stack_tape :
    (result node C D F L B n count Q clauses ref out source pre packet refs P).tapes 74=
      pre++List.replicate (2*ref+1+(state node out refs).erased) false := by
  have h:=result_slot node C D F L B n count Q clauses ref out source pre packet refs P 31
  change (result node C D F L B n count Q clauses ref out source pre packet refs P).tapes 74=
    ZeroPadding.pad 0 (stack pre []++List.replicate (2*ref+1+(state node out refs).erased) false) at h
  simpa only [ZeroPadding.pad_zero,stack,List.reverse_nil,RecoveryBoundedNativeUnaryLoop.stackWords,List.flatMap_nil,List.append_nil] using h

theorem graph_head :
    (result node C D F L B n count Q clauses ref out source pre packet refs P).heads 20=
      ((result node C D F L B n count Q clauses ref out source pre packet refs P).tapes 20).length := by
  have h:=head_slot node C D F L B n count Q clauses ref out source pre packet refs P 20
  have t:=result_slot node C D F L B n count Q clauses ref out source pre packet refs P 20
  change (result node C D F L B n count Q clauses ref out source pre packet refs P).heads 20=_ at h
  change (result node C D F L B n count Q clauses ref out source pre packet refs P).tapes 20=
    ZeroPadding.pad 0 ((after C refs.length ref pre (state node out refs)).tapes 20) at t
  rw [h,t,ZeroPadding.pad_zero]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountConjunction
