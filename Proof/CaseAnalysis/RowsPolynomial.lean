import Proof.CaseAnalysis.RowsDegreeLoop
import Proof.CaseAnalysis.RowsDegreeRange

/-! The executed degree loop prints exactly one polynomial's complete
signed-cut word, in the permitted positional order and with every duplicate
monomial occurrence retained. Its output cursor remains at the append end. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPolynomial
open LocalBitMultitape CloseoutRowsLoopLayout CloseoutRowsLoopBoundary
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def body := CloseoutRowsDegreeBody.machine worker
noncomputable def machine := CloseoutRowsDegreeLoop.machine body
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  RepeatMachine.cfg 0 (CloseoutRowsDegreeLoop.entry body gs p F w 0 C rows out) Q 1

theorem output_fields {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) :
    inputTapes gs p F w j C rows out 31=out ∧ inputHeads gs p F w j rows out 31=out.length := by
  have hf := RowTupleCutList.fields (0 : Fin 1) gs p F w rows.length (j+1) rows [] 0 out 0 ((-2 : ℤ)^j)
  rw [CloseoutRowsEnumeratedCuts.cfg_eq] at hf
  constructor
  · change ZeroPadding.pad 0 ((CloseoutRowsEnumeratedCuts.core (0 : Fin 1) gs p F w (j+1)
      rows [] 0 out 0 ((-2 : ℤ)^j)).tapes 31)=out
    simpa only [ZeroPadding.pad_zero] using hf.2.2.1
  · exact hf.2.2.2

theorem polynomial_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length)
    (hw : w=RowTupleSubsets.digitWidth rows.length) (hQp : Q≤p)
    (hp : RowTupleFixedCapacity.width gs Q≤p)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F)
    (hc : ∀ j<Q,CloseoutRowsComputedCuts.budget gs p F w j rows+1≤C)
    (ht : ∀ j<Q,∀ pre i,CloseoutRowsDegreeReset.selected i=true →
      ((rawInput gs p F w j rows pre).tapes i).length≤C)
    (hcopy : 4*w+3≤C) (hmeta : ∀ j<Q,2*w+p+j+3≤C)
    (h47 : ∀ j<Q,RowTupleCursorReady.capacity gs.length w rows.length (j+2)≤C) :
    ∃ actual,runFrom machine (CloseoutRowsDegreeLoop.budget Q C) (input gs p F Q w C rows out)=some actual ∧
      actual.final.tapes 31=out++
        (CloseoutRows.orderedCuts (RowCachedCoordinateBounds.width gs) Q
          (CloseoutRowsCacheInput.polynomial gs rows)).flatMap (MatrixScoreBatch.cutWord p) ∧
      actual.final.heads 31=(out++
        (CloseoutRows.orderedCuts (RowCachedCoordinateBounds.width gs) Q
          (CloseoutRowsCacheInput.polynomial gs rows)).flatMap (MatrixScoreBatch.cutWord p)).length ∧
      actual.final.heads 112=1 ∧ actual.final.tapes 112=CompareMachine.word Q ∧
      actual.steps≤CloseoutRowsDegreeLoop.budget Q C := by
  have hfit : rows.length<2^w := by rw [hw]; exact RowTupleSubsets.digit_fit rows.length
  obtain ⟨actual,ha,hf,hs⟩ := CloseoutRowsDegreeLoop.degrees_run gs p F Q w C rows out
    hl hM hfit hQp hp hF hc ht hcopy hmeta h47
  have hout : (List.range Q).flatMap (fun j=>emitted gs p w j rows)=
      (CloseoutRows.orderedCuts (RowCachedCoordinateBounds.width gs) Q
        (CloseoutRowsCacheInput.polynomial gs rows)).flatMap (MatrixScoreBatch.cutWord p) := by
    rw [hw]
    exact CloseoutRowsDegreeRange.polynomial_output gs p Q rows
  refine ⟨actual,ha,?_,?_,?_,?_,hs⟩
  · rw [hf]
    change inputTapes gs p F w Q C rows (out++(List.range Q).flatMap (fun j=>emitted gs p w j rows)) 31=_
    rw [(output_fields gs p F w Q C rows _).1,hout]
  · rw [hf]
    change inputHeads gs p F w Q rows (out++(List.range Q).flatMap (fun j=>emitted gs p w j rows)) 31=_
    rw [(output_fields gs p F w Q C rows _).2,hout]
  · rw [hf]
    rfl
  · rw [hf]
    rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsPolynomial
