import Proof.PCP.PCPPQueryClauseMatrixRetained
import Proof.PCP.PCPPQueryClauseLookupRetained
import Proof.PCP.PCPPQueryClauseSemantics

/-! Same-source clause access with both actual drivers retained. This is the
existing metadata/matrix/pair machine, with the endpoints needed for reuse. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryClause
open LocalBitMultitape RepairRepresentation PCPPQueryField RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem clause_retained_run (a b c arity : ℕ) (matrixRows : List (List Bool)) (count : ℕ)
    (rows : List (ℕ×ℕ)) (left right : ℕ) (tail : List Bool)
    (hcount : matrixRows.length=a) (hwidth : ∀ row∈matrixRows,row.length=arity) :
    let source := fourBits 3 a b c++matrixRows.flatten++natWord count++PCPPQueryClauseRows.stream rows++pairBits left right++tail
    ∃ r,runFrom machine (budget a b c arity count rows left right) (entry source arity rows.length)=some r ∧
      r.steps≤budget a b c arity count rows left right ∧ r.final.tapes 15=natListWord [left,right] ∧
      r.final.tapes 0=source ∧ r.final.tapes 13=UnaryTemplate.tape arity ∧
      r.final.heads 13=1 ∧ r.final.tapes 14=UnaryTemplate.tape rows.length ∧ r.final.heads 14=1 := by
  dsimp only
  let pre := fourBits 3 a b c++matrixRows.flatten
  let source := pre++natWord count++PCPPQueryClauseRows.stream rows++pairBits left right++tail
  obtain ⟨first,hfirst,hfs,hsource,hsourceHead,hscratch,hscratchHead,hdiscard,hdiscardHead,hindex,hindexHead,hout,houtHead,harity,harityHead⟩ :=
    PCPPQueryClauseMatrix.matrix_retained_run a b c arity rows.length matrixRows
      (natWord count++PCPPQueryClauseRows.stream rows++pairBits left right++tail) hcount hwidth
  have hword : fourBits 3 a b c++matrixRows.flatten++
      (natWord count++PCPPQueryClauseRows.stream rows++pairBits left right++tail)=source := by
    simp [source,pre,List.append_assoc]
  rw [hword] at hfirst hsource
  obtain ⟨base,hb,hbs,hbo,hbsource,hbindex,hbindexHead⟩ := PCPPQueryClauseLookup.lookup_retained_run pre count rows left right tail
    (saved c (saved b (saved 3 [])))
  obtain ⟨focused,hf,hff,hfs'⟩ := RecoveryFocus.run_config slots (by decide) PCPPQueryClauseLookup.machine
    first.final.heads first.final.tapes _ _ base hb
  have he : RecoveryFocus.config slots first.final.heads first.final.tapes
      (PCPPQueryClauseLookup.entry source pre.length (saved c (saved b (saved 3 []))) rows.length)=
      Composition.restart first.final lookup.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      fin_cases i
      · change first.final.heads 0=pre.length
        simpa [pre] using hsourceHead
      · exact hscratchHead
      · exact houtHead
      · exact hindexHead
      · exact hdiscardHead
    · intro i
      fin_cases i
      · exact hsource
      · exact hscratch
      · exact hout
      · exact hindex
      · exact hdiscard
  rw [he] at hf
  have hj := Composition.run_join PCPPQueryClauseMatrix.machine lookup _ _ _ first focused hfirst hf
  refine ⟨Composition.joinedReceipt first focused,hj,?_,?_,?_,?_,?_,?_,?_⟩
  · change first.steps+1+focused.steps≤_
    rw [hfs',hbs]
    unfold budget
    omega
  · change focused.final.tapes (slots 2)=_
    simp only [hff,RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
    exact hbo

  · change focused.final.tapes (slots 0)=_
    simp only [hff,RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
    exact hbsource
  · change focused.final.tapes 13=_
    have hn : RecoveryFocus.pick slots (13 : Fin 16)=none := by decide
    simpa only [hff,RecoveryFocus.config,hn] using harity
  · change focused.final.heads 13=_
    have hn : RecoveryFocus.pick slots (13 : Fin 16)=none := by decide
    simpa only [hff,RecoveryFocus.config,hn] using harityHead
  · change focused.final.tapes (slots 3)=_
    simp only [hff,RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
    exact hbindex
  · change focused.final.heads (slots 3)=_
    simp only [hff,RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
    exact hbindexHead

end NearCubicWires.RepairOrdinary.PCPPQueryClause
