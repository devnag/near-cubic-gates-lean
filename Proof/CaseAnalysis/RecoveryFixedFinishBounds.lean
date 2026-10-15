import Proof.CaseAnalysis.RecoveryFixedFinishOriginal

/-! The reusable original fixed-count continuation uses the existing
metadata bounds and the same coarse reference-stack backing. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedFixedFinish
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem row_work_bound (node C D F L B n count Q clauses : ℕ) (out source stack packet : List Bool)
    (hC : C+1≤B) (hD : D≤B) (hL : L≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,
      (RecoveryBoundedRowPrototype.fields C D F L n count Q clauses j).length≤B) :
    ∀ i,(RecoveryBoundedRows.rowData node C D F L B out n count Q clauses [] source stack packet
      (RecoveryBoundedRowErase.work i)).length≤B := by
  intro i
  rw [←ready_original node C D F L n count Q clauses B out source stack packet hC hD hL,
    RecoveryBoundedGrammarBank.ready_work]
  split_ifs with hi
  · have h:=hf _ hi
    simp only [ZeroPadding.pad,List.length_append,List.length_replicate]
    omega
  · simp only [List.length_replicate,le_refl]

theorem ambient_work_bound (node C D F L B n count Q clauses : ℕ)
    (out source stack packet : List Bool) (refs : List ℕ) (P : Fin 37→List Bool)
    (hC : C+1≤B) (hD : D≤B) (hL : L≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,
      (RecoveryBoundedRowPrototype.fields C D F L n count Q clauses j).length≤B) :
    ∀ i,(RecoveryBoundedRowsFold.ambient node C D F L B n count Q clauses out source stack packet refs P
      ((RecoveryBoundedRowErase.work i).castAdd 38)).length≤B := by
  intro i
  change (RecoveryBoundedRowsFold.ambient node C D F L B n count Q clauses out source stack packet refs P
    (((RecoveryBoundedRowErase.work i).castAdd 37).castAdd 1)).length≤B
  simp only [RecoveryBoundedRowsFold.ambient,RecoveryBoundedRows.scanData,Fin.addCases_left,
    RecoveryBoundedRows.data]
  exact row_work_bound node C D F L B n count Q clauses out source
    (stack++RecoveryBoundedClauseList.stackWord refs) packet hC hD hL hf i

theorem erased_bound (node W ref : ℕ) (out stack : List Bool) (refs : List ℕ) (P : ℕ)
    (hRef : ref≤W) (hrefs : ∀ r∈refs,r≤W)
    (hP : stack.length+(refs.length+1)*(2*W+1)≤P) :
    stack.length+(2*ref+1+(RecoveryBoundedCountConjunction.state node out refs).erased)≤P := by
  have h:=RecoveryBoundedSelectorLoop.erased_bound true W refs.reverse
    ⟨node,0,0,out++RecoveryBoundedGrammarFold.bits true⟩
    (by intro r hr;exact hrefs r (List.mem_reverse.mp hr))
  change (RecoveryBoundedCountConjunction.state node out refs).erased≤0+refs.reverse.length*(2*W+1) at h
  simp only [Nat.zero_add,List.length_reverse] at h
  simp only [Nat.add_mul,Nat.one_mul] at hP
  omega

theorem budget_bound (ref B : ℕ) (fields : Fin 78→List Bool) (hRef : 2*ref+2≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(fields j).length≤B) :
    RecoveryBoundedGrammarAfter.budget ref B fields≤64*(B+2) := by
  have h:=RecoveryBoundedRowReload.budget_bound fields B hf
  unfold RecoveryBoundedGrammarAfter.budget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedFixedFinish
