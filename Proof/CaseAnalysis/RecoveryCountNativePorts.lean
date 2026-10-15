import Proof.CaseAnalysis.RecoveryCountCompiled

/-! Physical final-count ports required by the unchanged serializer:
append cursor, raw output and untouched retained scalar/backing tapes. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountNativeFold
open LocalBitMultitape SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (node C D F L B P n count Q clauses total : ℕ) (out source pre packet : List Bool)
variable (refs : List ℕ) (proj : Fin 37→List Bool) (cold : Fin 33→List Bool) (bd cd : List Bool)

theorem head_slot (j : Fin 35) :
    (result node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd).heads (slots j)=
      (RecoveryBoundedGrammarFold.finalConfiguration false node C out pre refs).heads j := by
  simp only [result,RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,ZeroPadding.config]

theorem result_kept (i : Fin 153) (hi : ¬∃ j,slots j=i) :
    (result node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd).heads i=heads out pre refs i ∧
    (result node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd).tapes i=
      bank node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd i := by
  simp only [result,RecoveryFocus.config,RecoveryFocus.pick,dif_neg hi]
  exact ⟨True.intro,True.intro⟩

theorem graph_head :
    (result node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd).heads 20=
      ((result node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd).tapes 20).length := by
  have h:=head_slot node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd 20
  have t:=result_slot node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd 20
  change (result node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd).heads 20=_ at h
  change (result node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd).tapes 20=
    ZeroPadding.pad 0 ((RecoveryBoundedGrammarFold.finalConfiguration false node C out pre refs).tapes 20) at t
  rw [h,t,ZeroPadding.pad_zero]
  rfl

theorem output_head :
    (result node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd).heads 25=0 := by
  exact head_slot node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd 25

def retainedPorts : Fin 6→Fin 153:=![135,140,144,145,76,116]
theorem retained_away (i : Fin 6) : ¬∃ j,slots j=retainedPorts i := by
  fin_cases i <;> decide

theorem retained_heads (i : Fin 6) :
    (result node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd).heads (retainedPorts i)=0 := by
  rw [(result_kept node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd
    (retainedPorts i) (retained_away i)).1]
  fin_cases i <;> rfl

theorem retained_words :
    (fun i=> (result node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd).tapes (retainedPorts i))=
      (![cold 18,cold 23,cold 27,cold 28,List.replicate B true,List.replicate B false] : Fin 6→List Bool) := by
  have h76 : RecoveryBoundedGrammarBank.ready (RecoveryBoundedRowPrototype.fields C D F L n count Q clauses)
      node B out (pre++RecoveryBoundedClauseList.stackWord refs) packet source 76=List.replicate B true := by
    rw [RecoveryBoundedGrammarBank.ready_kept _ _ _ _ _ _ _ _ (by decide)]
    rfl
  funext i
  rw [(result_kept node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd
    (retainedPorts i) (retained_away i)).2]
  fin_cases i
  all_goals first
    | rfl
    | change ZeroPadding.pad 0 (RecoveryBoundedGrammarBank.ready
        (RecoveryBoundedRowPrototype.fields C D F L n count Q clauses) node B out
        (pre++RecoveryBoundedClauseList.stackWord refs) packet source 76)=List.replicate B true
      rw [ZeroPadding.pad_zero,h76]

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountNativeFold
