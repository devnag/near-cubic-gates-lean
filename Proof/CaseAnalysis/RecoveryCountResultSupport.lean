import Proof.CaseAnalysis.RecoveryCountResultPorts

/-! The original final AND returns a reusable bounded work bank. Only its
graph, output reference and erased reference stack can grow. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountConjunction
open LocalBitMultitape RecoveryRootRound RecoveryBoundedNativeFoldLoop
open RecoveryBoundedRowsFold (slots slots_injective caps)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem after_blank (C B total ref : ℕ) (pre : List Bool) (a : State) (hC : C+1≤B)
    (j : Fin 35) (h20 : j≠20) (h22 : j≠22) (h25 : j≠25) (h31 : j≠31) (h34 : j≠34) :
    ZeroPadding.pad (caps B j) ((after C total ref pre a).tapes j)=List.replicate B false := by
  fin_cases j
  all_goals first
    | exact False.elim (h20 rfl)
    | exact False.elim (h22 rfl)
    | exact False.elim (h25 rfl)
    | exact False.elim (h31 rfl)
    | exact False.elim (h34 rfl)
    | exact RecoveryBoundedSelectorLoop.pad_erased B C (by omega)
    | exact RecoveryBoundedSelectorLoop.pad_erased B (C+1) hC
    | exact RecoveryBoundedSelectorLoop.pad_erased B 0 (Nat.zero_le B)
    | exact RecoveryBoundedSelectorLoop.pad_erased B 1 (by omega)

variable (node C D F L B n count Q clauses ref : ℕ) (out source pre packet : List Bool)
variable (refs : List ℕ) (P : Fin 37→List Bool)

theorem scratch (hC : C+1≤B) :
    (result node C D F L B n count Q clauses ref out source pre packet refs P).tapes 73=
      List.replicate B false := by
  change (result node C D F L B n count Q clauses ref out source pre packet refs P).tapes (slots 1)=_
  rw [result_slot]
  exact after_blank C B refs.length ref pre (state node out refs) hC 1
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem literal_source :
    (result node C D F L B n count Q clauses ref out source pre packet refs P).tapes 70=source := by
  rw [result_other node C D F L B n count Q clauses ref out source pre packet refs P 70 (by decide)]
  change ZeroPadding.pad 0 (RecoveryBoundedRow.data node C D F L out n count [] [] Q source [] clauses 70)=source
  rw [ZeroPadding.pad_zero]
  have h:=RecoveryBoundedRow.clause_state node C D F L out [] n count [] [] Q source [] clauses
  exact h.sourceA

theorem backing_driver :
    (result node C D F L B n count Q clauses ref out source pre packet refs P).tapes 76=
      List.replicate B true := by
  rw [result_other node C D F L B n count Q clauses ref out source pre packet refs P 76 (by decide)]
  rfl

theorem backing_log :
    (result node C D F L B n count Q clauses ref out source pre packet refs P).tapes 77=
      List.replicate (B+1) false := by
  rw [result_other node C D F L B n count Q clauses ref out source pre packet refs P 77 (by decide)]
  rfl

theorem work_bound (hC : C+1≤B)
    (hA : ∀ i,(RecoveryBoundedRowsFold.ambient node C D F L B n count Q clauses out source
      (RecoveryBoundedClauseCollect.pushed ref pre) packet refs P
        ((RecoveryBoundedRowErase.work i).castAdd 38)).length≤B) :
    ∀ i,((result node C D F L B n count Q clauses ref out source pre packet refs P).tapes
      ((RecoveryBoundedRowErase.work i).castAdd 38)).length≤B := by
  intro i
  have hw:=RecoveryBoundedRowErase.work_spec i
  by_cases hin : ∃ j,slots j=(RecoveryBoundedRowErase.work i).castAdd 38
  · obtain ⟨j,hj⟩:=hin
    have h20 : j≠20:=by
      intro he;subst j
      exact hw.2.1 (Fin.ext (congrArg Fin.val hj).symm)
    have h25 : j≠25:=by
      intro he;subst j
      exact hw.2.2.1 (Fin.ext (congrArg Fin.val hj).symm)
    have h31 : j≠31:=by
      intro he;subst j
      have hv:=congrArg Fin.val hj
      change 74=(RecoveryBoundedRowErase.work i).val at hv
      omega
    have h34 : j≠34:=by
      intro he;subst j
      have hv:=congrArg Fin.val hj
      change 115=(RecoveryBoundedRowErase.work i).val at hv
      omega
    rw [←hj,result_slot]
    by_cases h22 : j=22
    · subst j
      change (ZeroPadding.pad B (List.replicate C true)).length≤B
      simp only [ZeroPadding.pad,List.length_append,List.length_replicate]
      omega
    · rw [after_blank C B refs.length ref pre (state node out refs) hC j h20 h22 h25 h31 h34,
        List.length_replicate]
  · rw [result_other node C D F L B n count Q clauses ref out source pre packet refs P _
      (by intro j hj;exact hin ⟨j,hj⟩)]
    exact hA i

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountConjunction
