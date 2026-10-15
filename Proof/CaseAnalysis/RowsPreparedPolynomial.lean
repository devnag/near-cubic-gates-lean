import Proof.CaseAnalysis.RowsPreparationInput
import Proof.CaseAnalysis.RowsScratch

/-! One whole polynomial executes at the actual common preparation capacity.
All degree, scratch, cursor and metadata inequalities are discharged here.
The enclosing bank still supplies the native source data and true C driver. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPreparedPolynomial
open LocalBitMultitape CloseoutRowsLoopLayout CloseoutRowsLoopBoundary
open CloseoutRowsPreparationBounds CloseoutRowsPreparationFits CloseoutRowsPreparationInput
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem polynomial_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (p F Q w : ℕ) (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length)
    (hw : rows.length<2^w) (hQp : Q ≤ p)
    (hp : RowTupleFixedCapacity.width gs Q ≤ p)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p ≤ F) :
    ∃ actual,runFrom CloseoutRowsPolynomial.machine
      (CloseoutRowsDegreeLoop.budget Q (capacity (l+r) p F w gs.length Q))
      (CloseoutRowsColdScratch.input gs p F Q w (capacity (l+r) p F w gs.length Q) rows out)=some actual ∧
      actual.final.tapes 31=out++(CloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p) ∧
      actual.final.heads 31=(out++(CloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p)).length ∧
      actual.final.tapes 112=CompareMachine.word Q ∧ actual.final.heads 112=1 ∧
      actual.steps ≤ CloseoutRowsDegreeLoop.budget Q (capacity (l+r) p F w gs.length Q) := by
  let C := capacity (l+r) p F w gs.length Q
  have hcopy : 4*w+3 ≤ C := by
    have h := small_fits (l+r) p F w gs.length Q
    unfold scale at h
    dsimp only [C]
    omega
  obtain ⟨source,hs,sf,ss⟩ := CloseoutRowsDegreeLoop.degrees_run gs p F Q w C rows out hl hM hw hQp hp hF
    (fun j hj=>computed_fits gs p F Q w j rows hl hw.le hj)
    (fun j hj=>selected_fits gs p F Q w j rows hw.le hj) hcopy
    (fun j hj=>(metadata_fits (l+r) p F w gs.length Q j hj).2)
    (fun j hj=>cursor_fits (l+r) p F w gs.length Q rows.length (j+2) hw.le (by omega))
  obtain ⟨actual,ha,ah,atape,ad,asteps,_⟩ := CloseoutRowsColdScratch.from_receipt gs p F Q w C _ rows out source hs
  have hout := CloseoutRowsSharedDigits.emitted_word gs p Q w rows
  refine ⟨actual,ha,?_,?_,?_,?_,asteps.le.trans ss⟩
  · rw [atape,sf]
    change inputTapes gs p F w Q C rows (out++(List.range Q).flatMap (fun j=>emitted gs p w j rows)) 31=_
    rw [(CloseoutRowsPolynomial.output_fields gs p F w Q C rows _).1,hout]
  · rw [ah,sf]
    change inputHeads gs p F w Q rows (out++(List.range Q).flatMap (fun j=>emitted gs p w j rows)) 31=_
    rw [(CloseoutRowsPolynomial.output_fields gs p F w Q C rows _).2,hout]
  · rw [ad,sf]
    rfl
  · rw [ah,sf]
    rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsPreparedPolynomial
