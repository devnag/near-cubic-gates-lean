import Proof.CaseAnalysis.RowsEstimatorResetHeads
import Proof.CaseAnalysis.RowsEstimatorReuseJoin

/-! The original physical estimator, private reset, six-field append and
owned scratch sweep, composed in one finite program. D and every row input
remain physically supplied by the enclosing metadata producer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
open LocalBitMultitape RepairRepresentation RecoveryRootRound CloseoutRowsEstimatorCoefficients
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first (a : WilliamsAlgorithm):=TapeEmbedding.machine 2 (Reset.machine a)
noncomputable def machine (a : WilliamsAlgorithm):=Composition.machine (first a) (after (producer a))
noncomputable def entry (a : WilliamsAlgorithm) (row : EquationRow.Input) (C D Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool) (out : List Bool):=
  Composition.leftConfig 24 (TapeEmbedding.config
    (![out.length,0] : Fin 2→ℕ) (![out,List.replicate D true] : Fin 2→List Bool)
    (Reset.entry a row C D Q q denominator select))

def budget (fuel b D : ℕ):=(2*fuel+2)+1+afterBudget b D

theorem record_private (p : Program) : (Whole.recordSlot p).val≠52 ∧ (Whole.recordSlot p).val≠68:=by
  unfold Whole.recordSlot WholePrefix.slots
  split_ifs <;>simp only [Fin.val_natAdd] <;>omega
theorem record_caps (p : Program) (D : ℕ) : Reset.caps p D (Whole.recordSlot p)=D:=by
  unfold Reset.caps
  exact if_neg (by rcases record_private p with ⟨h1,h2⟩;tauto)

theorem work_old (p : Program) (i : Fin (WholePrefix.tapes p-2)) :
    work p i=old p ⟨(work p i).val,(work_bounds p i).1⟩ := Fin.ext rfl

private theorem embedded_steps {t e s : ℕ} (H : Fin e → ℕ) (A : Fin e → List Bool)
    (r : ExecutionReceipt t s) : (TapeEmbedding.receipt H A r).steps=r.steps:=rfl

theorem run (a : WilliamsAlgorithm) (row : EquationRow.Input) (C D Q b : ℕ)
    (q : CompetitorValidity.Estimate) (count denominator : ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool) (out : List Bool)
    (fuel : ℕ) (source : ExecutionReceipt _ _)
    (hr:runFrom (Whole.machine a) fuel (Whole.entry a row C Q q denominator select)=some source)
    (hrecord:source.final.tapes (Whole.recordSlot (producer a))=Stream.recordWord b q count denominator)
    (hn:source.final.heads ((52 : Fin 70).castAdd (CloseoutRowsRawRecord.tapes (producer a)))=0)
    (hD:source.steps+1≤D) (hb:20*b+27≤D+1)
    (hsize:∀ i:Fin (WholePrefix.tapes (producer a)),i.val≠52→
      ((Whole.entry a row C Q q denominator select).tapes i).length≤D) :
    ∃ r,runFrom (machine a) (budget fuel b D) (entry a row C D Q q denominator select out)=some r ∧
      r.steps≤4*D+40*b+64 ∧
      r.final.heads=(fun i=>if i=output (producer a) then (out++Stream.recordWord b q count denominator).length else 0) ∧
      r.final.tapes (output (producer a))=out++Stream.recordWord b q count denominator ∧
      (∀ i,r.final.tapes (work (producer a) i)=List.replicate D false) ∧
      r.final.tapes (driver (producer a))=List.replicate D true ∧
      r.final.tapes (log (producer a))=List.replicate (D+1) false:=by
  let p:=producer a
  obtain ⟨reset,rr,rs,rt,rh,rsize,rl⟩:=Reset.run a row C D Q q denominator select fuel source hr hD hsize
  obtain ⟨rheads,rloghead⟩:=Reset.heads a row C D Q q denominator select fuel source hr hD reset rr
  have reset_heads:∀ i,reset.final.heads i=0:=by
    intro i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · by_cases hj:j.val=52
      · have he:j=(52 : Fin 70).castAdd (CloseoutRowsRawRecord.tapes p):=Fin.ext hj
        have hn':source.final.heads j=0:=by rw [he];exact hn
        exact (rheads j).trans (by simp only [Reset.selected,hj,ne_eq,not_true_eq_false,decide_false];exact hn')
      · exact (rheads j).trans (if_pos (decide_eq_true hj))
    · rw [Subsingleton.elim j (0 : Fin 1)]
      exact rloghead
  have fs:=runFrom_steps_le _ _ _ _ hr
  have rr':runFrom (Reset.machine a) (2*fuel+2) (Reset.entry a row C D Q q denominator select)=some reset:=by
    have hm:=runFrom_moreFuel (Reset.machine a) (2*source.steps+2)
      (2*fuel+2-(2*source.steps+2)) _ reset rr
    have he:2*source.steps+2+(2*fuel+2-(2*source.steps+2))=2*fuel+2:=by omega
    rw [he] at hm
    exact hm
  let before:=TapeEmbedding.receipt (![out.length,0] : Fin 2→ℕ)
    (![out,List.replicate D true] : Fin 2→List Bool) reset
  have hfirst:=TapeEmbedding.run_embed (Reset.machine a) (![out.length,0] : Fin 2→ℕ)
    (![out,List.replicate D true] : Fin 2→List Bool) _ _ reset rr'
  have bh:∀ i,i≠output p→ before.final.heads i=0:=by
    intro i
    refine Fin.addCases (fun j hj=>?_) (fun j hj=>?_) i
    · exact (TapeEmbedding.receipt_heads_old _ _ reset j).trans (reset_heads j)
    · fin_cases j
      · exact False.elim (hj rfl)
      · exact TapeEmbedding.receipt_heads_new _ _ reset 1
  have bo:before.final.heads (output p)=out.length:=TapeEmbedding.receipt_heads_new _ _ reset 0
  have bword:before.final.tapes (old p (Whole.recordSlot p))=
      ZeroPadding.pad D (Stream.recordWord b q count denominator):=by
    have h:=(TapeEmbedding.receipt_tapes_old (![out.length,0] : Fin 2→ℕ)
        (![out,List.replicate D true] : Fin 2→List Bool) reset ((Whole.recordSlot p).castAdd 1)).trans (rt (Whole.recordSlot p))
    rw [record_caps,hrecord] at h
    exact h
  have blog:before.final.tapes (log p)=List.replicate (D+1) false:=
    (TapeEmbedding.receipt_tapes_old (![out.length,0] : Fin 2→ℕ)
        (![out,List.replicate D true] : Fin 2→List Bool) reset ((0 : Fin 1).natAdd (WholePrefix.tapes p))).trans rl
  have bsize:∀ i,(before.final.tapes (work p i)).length≤D:=by
    intro i
    let j:Fin (WholePrefix.tapes p):=⟨(work p i).val,(work_bounds p i).1⟩
    have he:work p i=old p j:=work_old p i
    have ht:before.final.tapes (work p i)=reset.final.tapes (j.castAdd 1):=by
      rw [he]
      exact TapeEmbedding.receipt_tapes_old (![out.length,0] : Fin 2→ℕ)
        (![out,List.replicate D true] : Fin 2→List Bool) reset (j.castAdd 1)
    exact (congrArg List.length ht).le.trans (rsize j (work_bounds p i).2.1)
  have hbefore : before.steps≤2*D+2 :=
    (embedded_steps (![out.length,0] : Fin 2→ℕ)
      (![out,List.replicate D true] : Fin 2→List Bool) reset).trans_le (by omega)
  exact join_run_bounded p (first a) _ (2*fuel+2) b D q count denominator out before hfirst hb hbefore
    bh bo bword
    (TapeEmbedding.receipt_tapes_new (![out.length,0] : Fin 2→ℕ)
      (![out,List.replicate D true] : Fin 2→List Bool) reset 0) blog
    (TapeEmbedding.receipt_tapes_new (![out.length,0] : Fin 2→ℕ)
      (![out,List.replicate D true] : Fin 2→List Bool) reset 1) bsize

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
