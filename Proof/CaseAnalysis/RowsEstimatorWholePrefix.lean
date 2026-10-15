import Proof.CaseAnalysis.RowsEstimatorBudget

/-! Dock the actual cold native-stream prefix directly into the existing
raw-row estimator bank. Every non-source metadata word remains explicit;
only the original source frame is produced by this paid prefix. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WholePrefix
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (p : Program):=70+CloseoutRowsRawRecord.tapes p
def slots (p : Program) (i : Fin (CloseoutRowsRawRecord.tapes p)) : Fin (tapes p):=
  if i.val=0 then ⟨66,by unfold tapes;omega⟩ else i.natAdd 70

theorem injective (p : Program) : Function.Injective (slots p):=by
  intro i j he
  have hv:=congrArg Fin.val he
  simp only [slots] at hv
  split_ifs at hv <;> simp only [Fin.val_natAdd] at hv <;> apply Fin.ext <;> omega

def extra (p : Program) (data : Fin (CloseoutRowsRawRecord.tapes p)→List Bool)
    (i : Fin (CloseoutRowsRawRecord.tapes p)):=if i.val=0 then [] else data i
def input (p : Program) (row : EquationRow.Input) (C : ℕ)
    (data : Fin (CloseoutRowsRawRecord.tapes p)→List Bool):=
  fun i=>Fin.addCases (m:=70) (n:=CloseoutRowsRawRecord.tapes p) (motive:=fun _=>List Bool)
    (Cold.input row C) (extra p data) i
def heads (p : Program) (row : EquationRow.Input):=
  fun i=>Fin.addCases (m:=70) (n:=CloseoutRowsRawRecord.tapes p) (motive:=fun _=>ℕ)
    (Cold.heads row) (fun _=>0) i
noncomputable def first (p : Program):=TapeEmbedding.machine (CloseoutRowsRawRecord.tapes p) Cold.machine
noncomputable def last {s : ℕ} (p : Program) (callee : Machine (CloseoutRowsRawRecord.tapes p) s):=
  RecoveryFocus.machine (slots p) callee
noncomputable def machine {s : ℕ} (p : Program) (callee : Machine (CloseoutRowsRawRecord.tapes p) s):=
  Composition.machine (first p) (last p callee)
noncomputable def entry {s : ℕ} (p : Program) (callee : Machine (CloseoutRowsRawRecord.tapes p) s)
    (row : EquationRow.Input) (C : ℕ) (data : Fin (CloseoutRowsRawRecord.tapes p)→List Bool):=
  (⟨(machine p callee).start,heads p row,input p row C data⟩ : Configuration (tapes p) _)

theorem prefix_run {s : ℕ} (p : Program) (callee : Machine (CloseoutRowsRawRecord.tapes p) s)
    (row : EquationRow.Input) (C : ℕ) (hC:(Header.stream row).length≤C)
    (data : Fin (CloseoutRowsRawRecord.tapes p)→List Bool)
    (source:∀ i,i.val=0→data i=frame (EquationRowRaw.source row))
    (fuel : ℕ) (child : ExecutionReceipt (CloseoutRowsRawRecord.tapes p) s)
    (ch:run callee fuel data=some child) : ∃ actual,
    runFrom (machine p callee) (Cold.budget row C+1+fuel) (entry p callee row C data)=some actual ∧
    actual.steps≤Cold.budget row C+1+child.steps ∧
    (∀ i,actual.final.heads (slots p i)=child.final.heads i) ∧
    (∀ i,actual.final.tapes (slots p i)=child.final.tapes i):=by
  let ext:=extra p data
  obtain ⟨base,hbase,bt,_bC,bh,bs⟩:=Cold.run row C hC
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
  obtain ⟨tail,th,_,ts,hh,tt,_⟩:=RecoveryFocus.dock (slots p) (injective p)
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
  refine ⟨Composition.joinedReceipt before tail,hj,?_,hh,tt⟩
  change base.steps+1+tail.steps≤_
  rw [ts]
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WholePrefix
