import Proof.CaseAnalysis.RecoveryCountRowEntry

/-! The original fixed-count result exposes the exact saved-output
continuation ports, including the retained projector and prototype. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountConjunction
open LocalBitMultitape RecoveryRootRound RecoveryExecution RepairRepresentation RecoveryBoundedNativeFoldLoop
open RepairSource.VerifierDecoding
open RecoveryBoundedRowsFold (slots slots_injective caps)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem after_heads (C total ref : ℕ) (pre : List Bool) (a : State) (j : Fin 35) :
    (after C total ref pre a).heads j=
      if j=20 then (a.next true ref).out.length else if j=31 then pre.length else if j=34 then 1 else 0 := by
  simp only [after,configuration,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,State.entry,
    RecoveryBoundedNativeFold.entry,RecoveryBoundedNativeFold.heads,stack,List.reverse_nil,
    RecoveryBoundedNativeUnaryLoop.stackWords,List.flatMap_nil,List.append_nil]
  fin_cases j <;> rfl

theorem ambient_heads (out pre : List Bool) (refs : List ℕ) (i : Fin 116) :
    RecoveryBoundedRowsFold.ambientHeads out pre refs i=
      if i=20 then out.length else if i=74 then (pre++RecoveryBoundedClauseList.stackWord refs).length
      else if i=115 then 1 else 0 := by
  fin_cases i <;> rfl

variable (node C D F L B n count Q clauses ref : ℕ) (out source pre packet : List Bool)
variable (refs : List ℕ) (P : Fin 37→List Bool)

theorem result_other (i : Fin 116) (hi : ∀ j,slots j≠i) :
    (result node C D F L B n count Q clauses ref out source pre packet refs P).tapes i=
      RecoveryBoundedRowsFold.ambient node C D F L B n count Q clauses out source
        (RecoveryBoundedClauseCollect.pushed ref pre) packet refs P i := by
  have hn : ¬∃ j,slots j=i:=by rintro ⟨j,hj⟩;exact hi j hj
  simp only [result,input,RecoveryBoundedRowsFold.result,RecoveryFocus.config,RecoveryFocus.pick,dif_neg hn]

theorem result_heads :
    (result node C D F L B n count Q clauses ref out source pre packet refs P).heads=
      fun i=>if i=20 then ((result node C D F L B n count Q clauses ref out source pre packet refs P).tapes 20).length
        else if i=74 then pre.length else if i=115 then 1 else 0 := by
  funext i
  by_cases h20 : i=20
  · subst i
    simp only [↓reduceIte]
    exact graph_head node C D F L B n count Q clauses ref out source pre packet refs P
  by_cases h74 : i=74
  · subst i
    simp only [if_neg (by decide : (74 : Fin 116)≠20),↓reduceIte]
    exact stack_head node C D F L B n count Q clauses ref out source pre packet refs P
  by_cases h115 : i=115
  · subst i
    simp only [if_neg (by decide : (115 : Fin 116)≠20),if_neg (by decide : (115 : Fin 116)≠74),↓reduceIte]
    exact head_slot node C D F L B n count Q clauses ref out source pre packet refs P 34
  simp only [if_neg h20,if_neg h74,if_neg h115]
  by_cases hin : ∃ j,slots j=i
  · obtain ⟨j,hj⟩:=hin
    subst i
    rw [head_slot,after_heads]
    have j20 : j≠20:=fun he=>h20 (by rw [he];rfl)
    have j31 : j≠31:=fun he=>h74 (by rw [he];rfl)
    have j34 : j≠34:=fun he=>h115 (by rw [he];rfl)
    rw [if_neg j20,if_neg j31,if_neg j34]
  · simp only [result,input,RecoveryBoundedRowsFold.result,RecoveryFocus.config,RecoveryFocus.pick,dif_neg hin]
    rw [ambient_heads,if_neg h20,if_neg h74,if_neg h115]

theorem projector (j : Fin 37) :
    (result node C D F L B n count Q clauses ref out source pre packet refs P).tapes
      (RecoveryBoundedRowRandomReset.outerSlots j)=P j := by
  have hi : ∀ k,slots k≠RecoveryBoundedRowRandomReset.outerSlots j:=by
    intro k he
    have hv:=congrArg Fin.val he
    change (slots k).val=78+j.val at hv
    by_cases hk : k=1
    · subst k;change 73=78+j.val at hv;omega
    by_cases hk31 : k=31
    · subst k;change 74=78+j.val at hv;omega
    by_cases hk34 : k=34
    · subst k;change 115=78+j.val at hv;omega
    · simp only [slots,if_neg hk,if_neg hk31,if_neg hk34,Fin.val_castAdd] at hv
      omega
  rw [result_other node C D F L B n count Q clauses ref out source pre packet refs P _ hi]
  simp only [RecoveryBoundedRowsFold.ambient,RecoveryBoundedRowRandomReset.outerSlots,
    RecoveryBoundedRows.scanData,RecoveryBoundedRows.projectionSlots,RecoveryBoundedRows.data,
    Fin.addCases_left,Fin.addCases_right]

theorem prototype :
    (result node C D F L B n count Q clauses ref out source pre packet refs P).tapes 75=packet := by
  rw [result_other node C D F L B n count Q clauses ref out source pre packet refs P 75 (by decide)]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountConjunction
