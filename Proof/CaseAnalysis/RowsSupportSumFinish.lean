import Proof.CaseAnalysis.RowsSupportTermMeaning

/-! The existing final mass test acts on the retained term bank. Both
embeddings use the original nested layout, so no tape copy or vector
reassociation is executed. The literal term driver is retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumBody
open LocalBitMultitape CompetitorSumFold RepairSource.VerifierDecoding
open CompetitorValidity (Estimate)
open CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def ending (k : ℕ) (q : ℚ) :=
  TapeEmbedding.machine 1 (TapeEmbedding.machine 1 (TapeEmbedding.machine 1705 (SumFinish.machine k q)))
def heads (position : ℕ) (out : List Bool) (extra : Fin 1705 → ℕ) (supports : List Bool) : Fin 2534 → ℕ :=
  Fin.addCases (m:=2533) (n:=1) (motive:=fun _=>ℕ) (Term.lift (TermRound.heads position out extra) supports.length) (fun _=>1)
def data (P K : ℕ) (terms : Fin 725 → List Bool) (ambient : Fin 94 → List Bool)
    (out : List Bool) (extra : Fin 1705 → List Bool) (supports : List Bool) : Fin 2534 → List Bool :=
  Fin.addCases (m:=2533) (n:=1) (motive:=fun _=>List Bool) (Term.lift (TermRound.data P terms ambient out extra) supports)
    (fun _=>CompareMachine.word K)

theorem finish_run (P B b k position K : ℕ) (q : ℚ) (a : Estimate)
    (source out : List Bool) (ambient : Fin 94 → List Bool)
    (extraHeads : Fin 1705 → ℕ) (extraTapes : Fin 1705 → List Bool)
    (supports : List Bool)
    (h : Store B a [] ambient) (ha : a.Valid B) (hB : 1 ≤ B) (hq : 0 ≤ q) (hk : k ≤ B)
    (hp : CompetitorThresholdDecision.numerator q < 2^k) (hd : q.den < 2^k)
    (hc : MassCheck.budget B k+1 ≤ P) (hi : ∀ i,(ambient i).length ≤ P) :
    ∃ next r,runFrom (ending k q) (SumFinish.budget P B k)
      ⟨(ending k q).start,heads position out extraHeads supports,
        data P K (TermRead.data P b [] source true) ambient out extraTapes supports⟩=some r ∧
      r.steps ≤ SumFinish.budget P B k ∧ r.final.heads=heads position out extraHeads supports ∧
      r.final.tapes=data P K (TermRead.data P b [] source (decide (a.value ≤ q))) next out extraTapes supports ∧
      Store B CompetitorSumWidth.zero [] next := by
  classical
  obtain ⟨next,⟨base,hbase,bs,bh,bt⟩,store⟩ := SumFinish.finish_run P B b k position q a source out true ambient
    h ha hB hq hk hp hd hc hi
  let middle := TapeEmbedding.receipt extraHeads extraTapes base
  have hm := TapeEmbedding.run_embed (SumFinish.machine k q) extraHeads extraTapes _ _ base hbase
  let kept:=TapeEmbedding.receipt (fun _ : Fin 1=>supports.length) (fun _=>supports) middle
  have keptRun:=TapeEmbedding.run_embed (TapeEmbedding.machine 1705 (SumFinish.machine k q))
    (fun _ : Fin 1=>supports.length) (fun _=>supports) _ _ middle hm
  let r := TapeEmbedding.receipt (fun _ : Fin 1=>1) (fun _=>CompareMachine.word K) kept
  have hr := TapeEmbedding.run_embed (TapeEmbedding.machine 1 (TapeEmbedding.machine 1705 (SumFinish.machine k q)))
    (fun _ : Fin 1=>1) (fun _=>CompareMachine.word K) _ _ kept keptRun
  refine ⟨next,r,hr,bs,?_,?_,store⟩
  · change Fin.addCases (m:=2533) (n:=1) (motive:=fun _=>ℕ)
      (Term.lift (Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>ℕ) base.final.heads extraHeads) supports.length) (fun _=>1)=_
    rw [bh];rfl
  · change Fin.addCases (m:=2533) (n:=1) (motive:=fun _=>List Bool)
      (Term.lift (Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>List Bool) base.final.tapes extraTapes) supports)
        (fun _=>CompareMachine.word K)=_
    rw [bt];rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumBody
