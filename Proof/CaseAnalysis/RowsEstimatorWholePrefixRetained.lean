import Proof.CaseAnalysis.RowsEstimatorWholePrefix

/-! Retain the original native source/head and capacity projections through
exactly the same cold-prefix and table docking. These are the external ports
needed when the private estimator bank is cleared. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WholePrefixRetained
open LocalBitMultitape WholePrefix
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem run {s : ℕ} (p : Program) (callee : Machine (CloseoutRowsRawRecord.tapes p) s)
    (row : EquationRow.Input) (C : ℕ) (hC:(Header.stream row).length≤C)
    (data : Fin (CloseoutRowsRawRecord.tapes p)→List Bool)
    (source:∀ i,i.val=0→data i=frame (EquationRowRaw.source row))
    (fuel : ℕ) (child : ExecutionReceipt (CloseoutRowsRawRecord.tapes p) s)
    (ch:run callee fuel data=some child) : ∃ actual,
    runFrom (machine p callee) (Cold.budget row C+1+fuel) (entry p callee row C data)=some actual ∧
    actual.steps≤Cold.budget row C+1+child.steps ∧
    (∀ i,actual.final.heads (slots p i)=child.final.heads i) ∧
    (∀ i,actual.final.tapes (slots p i)=child.final.tapes i) ∧
    (∀ i : Fin 70,i.val≠66→ actual.final.heads (i.castAdd (CloseoutRowsRawRecord.tapes p))=0) ∧
    actual.final.tapes ((68 : Fin 70).castAdd (CloseoutRowsRawRecord.tapes p))=List.replicate C true:=by
  let ext:=extra p data
  obtain ⟨base,hbase,bt,bC,bh,bs⟩:=Cold.run row C hC
  let before:=TapeEmbedding.receipt (fun _ : Fin (CloseoutRowsRawRecord.tapes p)=>0) ext base
  have hfirst:=TapeEmbedding.run_embed Cold.machine
    (fun _ : Fin (CloseoutRowsRawRecord.tapes p)=>0) ext _ _ base hbase
  have hheads:∀ i,before.final.heads (slots p i)=0:=by
    intro i
    by_cases hz:i.val=0
    · simp only [slots,hz,ite_true]
      change before.final.heads ((66 : Fin 70).castAdd (CloseoutRowsRawRecord.tapes p))=0
      exact (TapeEmbedding.receipt_heads_old _ _ base 66).trans (bh 66)
    · simp only [slots,hz,ite_false]
      exact TapeEmbedding.receipt_heads_new _ _ base i
  have htapes:∀ i,before.final.tapes (slots p i)=data i:=by
    intro i
    by_cases hz:i.val=0
    · simp only [slots,hz,ite_true]
      change before.final.tapes ((66 : Fin 70).castAdd (CloseoutRowsRawRecord.tapes p))=_
      exact (TapeEmbedding.receipt_tapes_old _ _ base 66).trans (bt.trans (source i hz).symm)
    · simp only [slots,hz,ite_false]
      rw [TapeEmbedding.receipt_tapes_new]
      simp only [ext,extra,hz,ite_false]
  obtain ⟨tail,th,_,ts,hh,tt,keep⟩:=RecoveryFocus.dock (slots p) (injective p)
    callee fuel before.final.heads before.final.tapes _ hheads htapes child ch
  have htail:runFrom (last p callee) fuel
      (Composition.restart before.final (last p callee).start)=some tail:=th
  have hj:=Composition.run_join (first p) (last p callee) _ _ _ before tail hfirst htail
  have hi:Composition.leftConfig _ (TapeEmbedding.config
      (fun _ : Fin (CloseoutRowsRawRecord.tapes p)=>0) ext (Cold.entry row C))=
      entry p callee row C data:=by
    apply configuration_ext
    · rfl
    · rfl
    · rfl
  rw [hi] at hj
  have avoid (i : Fin 70) (hi:i.val≠66) : ∀ j,slots p j≠i.castAdd (CloseoutRowsRawRecord.tapes p):=by
    intro j he
    have hv:=congrArg Fin.val he
    simp only [slots,Fin.val_castAdd] at hv
    split_ifs at hv <;>simp only [Fin.val_natAdd] at hv <;>have ht:=i.isLt <;>omega
  refine ⟨Composition.joinedReceipt before tail,hj,?_,hh,tt,?_,?_⟩
  · change base.steps+1+tail.steps≤_
    rw [ts]
    omega
  · intro i hi
    change tail.final.heads (i.castAdd (CloseoutRowsRawRecord.tapes p))=0
    exact (keep _ (avoid i hi)).1.trans
      ((TapeEmbedding.receipt_heads_old _ _ base i).trans (bh i))
  · change tail.final.tapes ((68 : Fin 70).castAdd (CloseoutRowsRawRecord.tapes p))=_
    exact (keep _ (avoid 68 (by decide))).2.trans
      ((TapeEmbedding.receipt_tapes_old _ _ base 68).trans bC)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WholePrefixRetained
