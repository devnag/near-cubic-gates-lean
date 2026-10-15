import Proof.CaseAnalysis.RowsEstimatorHeader

/-! The existing raw-row/Williams prefix with literal caller metadata.
Only the original physical request is supplied at bank zero; its actual
count-table consumer remains responsible for producing every count byte. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Consumer
open LocalBitMultitape MatrixScoreBatch
open CloseoutRowsRawRecord (tapes receive receive_injective first last machine)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (p : Program) (data : Fin (CompetitorCountTableRecord.tapes p)→List Bool)
    (i : Fin (CompetitorCountTableRecord.tapes p)):=if i.val=0 then [] else data i
def input (p : Program) (row : EquationRow.Input)
    (data : Fin (CompetitorCountTableRecord.tapes p)→List Bool):=
  fun i=>Fin.addCases (m:=130) (n:=CompetitorCountTableRecord.tapes p) (motive:=fun _=>List Bool)
    (EquationRowFramed.input row) (extra p data) i

theorem prefix_run {s : ℕ} (p : Program) (callee : Machine (CompetitorCountTableRecord.tapes p) s)
    (row : EquationRow.Input) (data : Fin (CompetitorCountTableRecord.tapes p)→List Bool)
    (source : ∀ i,i.val=0→data i=physicalInput (EquationRow.request row))
    (fuel : ℕ) (child : ExecutionReceipt (CompetitorCountTableRecord.tapes p) s)
    (ch : run callee fuel data=some child) :
    ∃ actual,run (machine p callee) (EquationRowFramed.uniformBudget row+1+fuel)
      (input p row data)=some actual ∧
      actual.steps≤EquationRowFramed.uniformBudget row+1+child.steps ∧
      (∀ i,actual.final.heads (receive p i)=child.final.heads i) ∧
      (∀ i,actual.final.tapes (receive p i)=child.final.tapes i) := by
  let ext := extra p data
  obtain ⟨base,hbase,bt,bh,bs⟩ := EquationRowFramed.producer_run row
  let before : ExecutionReceipt (tapes p) _ := TapeEmbedding.receipt
    (fun _ : Fin (CompetitorCountTableRecord.tapes p) => 0) ext base
  have hfirst := TapeEmbedding.run_embed EquationRowFramed.machine
    (fun _ : Fin (CompetitorCountTableRecord.tapes p) => 0) ext _ _ base hbase
  have hheads : ∀ i,before.final.heads (receive p i)=0 := by
    intro i
    by_cases hz : i.val=0
    · simp only [receive,hz,↓reduceIte]
      change before.final.heads ((128 : Fin 130).castAdd (CompetitorCountTableRecord.tapes p))=0
      rw [TapeEmbedding.receipt_heads_old]
      exact bh 128
    · simp only [receive,hz,↓reduceIte]
      exact TapeEmbedding.receipt_heads_new _ ext base i
  have htapes : ∀ i,before.final.tapes (receive p i)=
      data i := by
    intro i
    by_cases hz : i.val=0
    · simp only [receive,hz,↓reduceIte]
      change before.final.tapes ((128 : Fin 130).castAdd (CompetitorCountTableRecord.tapes p))=_
      rw [TapeEmbedding.receipt_tapes_old,bt]
      exact (source i hz).symm
    · simp only [receive,hz,↓reduceIte]
      rw [TapeEmbedding.receipt_tapes_new]
      simp only [ext,extra,hz,↓reduceIte]
  obtain ⟨tail,th,_,ts,hh,tt,_⟩ := RecoveryFocus.dock (receive p) (receive_injective p)
    callee fuel before.final.heads before.final.tapes _ hheads htapes child ch
  have htail : runFrom (last p callee) fuel
      (Composition.restart before.final (last p callee).start)=some tail := th
  have hj := Composition.run_join (first p) (last p callee) _ _ _ before tail hfirst htail
  have hi : Composition.leftConfig _ (TapeEmbedding.config
      (fun _ : Fin (CompetitorCountTableRecord.tapes p) => 0) ext
      (initialConfiguration EquationRowFramed.machine (EquationRowFramed.input row)))=
      initialConfiguration (machine p callee) (input p row data) := by
    apply configuration_ext
    · rfl
    · funext i
      change Fin.addCases (m := 130) (n := CompetitorCountTableRecord.tapes p)
        (motive := fun _ => ℕ) (fun _ => 0) (fun _ => 0) i=0
      refine Fin.addCases (m := 130) (n := CompetitorCountTableRecord.tapes p) ?_ ?_ i <;>
        intro j <;> simp only [Fin.addCases_left,Fin.addCases_right]
    · rfl
  rw [hi] at hj
  refine ⟨Composition.joinedReceipt before tail,hj,?_,hh,tt⟩
  change base.steps+1+tail.steps≤_
  rw [ts]
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Consumer
