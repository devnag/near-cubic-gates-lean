import Proof.CaseAnalysis.RowsDegreeClean
import Proof.CaseAnalysis.RowsCutMeaning

/-! Actual fixed-degree cut production followed by paid scratch reuse.
The native cache and the row append cursor survive; the next call reloads
only degree metadata into the erased work bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsReusableCuts
open LocalBitMultitape RecoveryExecution CloseoutRowsDegreeReset
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := CloseoutRowsDegreeClean.machine CloseoutRowsComputedCuts.machine
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  CloseoutRowsDegreeClean.input
    (CloseoutRowsComputedCuts.input CloseoutRowsComputedCuts.machine.start gs p F w j rows out) C
def budget {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j C : ℕ) (rows : List (List Bool)) :=
  CloseoutRowsDegreeClean.budget (CloseoutRowsComputedCuts.budget gs p F w j rows) C

theorem finished_output {s n : ℕ} (state : Fin s) (gs : List (ExactThresholdGate n))
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) :
    (CloseoutRowsEnumeratedCuts.finished state gs p F w (j+1) rows out ((-2 : ℤ)^j)).tapes 31=
        out++RowTupleCutList.output gs p rows (RowTupleSubsets.selected w rows.length (j+1)) ((-2 : ℤ)^j) ∧
    (CloseoutRowsEnumeratedCuts.finished state gs p F w (j+1) rows out ((-2 : ℤ)^j)).heads 31=
        (out++RowTupleCutList.output gs p rows (RowTupleSubsets.selected w rows.length (j+1)) ((-2 : ℤ)^j)).length := by
  have h := RowTupleCutList.fields state gs p F w rows.length (j+1) rows
    (RowTupleEnumeration.word w (j+1) rows.length) (RowTupleEnumeration.word w (j+1) rows.length).length
    (out++RowTupleCutList.output gs p rows (RowTupleSubsets.selected w rows.length (j+1)) ((-2 : ℤ)^j))
    (RowTupleCutList.finalBound rows (RowTupleSubsets.selected w rows.length (j+1)) 0) ((-2 : ℤ)^j)
  simpa only [CloseoutRowsEnumeratedCuts.cfg_eq,CloseoutRowsEnumeratedCuts.finished] using h.2.2

theorem fixed_degree_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (p F Q w j C : ℕ) (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length)
    (hw : rows.length<2^w) (hj : j<Q) (hQp : Q≤p)
    (hp : RowTupleFixedCapacity.width gs Q≤p)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F)
    (hc : CloseoutRowsComputedCuts.budget gs p F w j rows+1≤C)
    (ht : ∀ i,selected i=true →
      ((CloseoutRowsComputedCuts.input CloseoutRowsComputedCuts.machine.start gs p F w j rows out).tapes i).length≤C) :
    ∃ actual,runFrom machine (budget gs p F w j C rows) (input gs p F w j C rows out)=some actual ∧
      actual.final.tapes 31=out++(CloseoutRowsCutMeaning.degreeCuts gs w j rows).flatMap (MatrixScoreBatch.cutWord p) ∧
      actual.final.heads 31=(out++(CloseoutRowsCutMeaning.degreeCuts gs w j rows).flatMap (MatrixScoreBatch.cutWord p)).length ∧
      (∀ i,actual.final.heads ((work i).castAdd 3)=0 ∧
        actual.final.tapes ((work i).castAdd 3)=List.replicate C false) ∧
      actual.final.tapes 103=List.replicate C false ∧
      actual.final.tapes 104=List.replicate C true ∧
      actual.final.tapes 105=List.replicate (C+1) false ∧
      actual.steps≤budget gs p F w j C rows := by
  obtain ⟨raw,hr,rh,rt,_⟩ := CloseoutRowsComputedCuts.cuts_run gs p F Q w j rows out hl hM hw hj hQp hp hF
  obtain ⟨actual,ha,ah,atapes,_,log1,_,driver,_,log2,hs⟩ := CloseoutRowsDegreeClean.clean_run
    CloseoutRowsComputedCuts.machine _ _ C raw hr
    (CloseoutRowsDegreeReset.input_heads _ gs p F w j rows out) ht hc
  have hout := finished_output CloseoutRowsComputedCuts.machine.start gs p F w j rows out
  have rawT : raw.final.tapes 31=out++RowTupleCutList.output gs p rows
      (RowTupleSubsets.selected w rows.length (j+1)) ((-2 : ℤ)^j) := (rt 31).trans hout.1
  have rawH : raw.final.heads 31=(out++RowTupleCutList.output gs p rows
      (RowTupleSubsets.selected w rows.length (j+1)) ((-2 : ℤ)^j)).length := (rh 31).trans hout.2
  refine ⟨actual,ha,?_,?_,?_,log1,driver,log2,hs⟩
  · have h := atapes 31
    change actual.final.tapes 31=raw.final.tapes 31 at h
    rw [h,rawT,CloseoutRowsCutMeaning.degree_output]
  · have h := ah 31
    change actual.final.heads 31=raw.final.heads 31 at h
    rw [h,rawH,CloseoutRowsCutMeaning.degree_output]
  · intro i
    have hh := ah (work i)
    have htape := atapes (work i)
    simpa [work_selected] using And.intro hh htape

end NearCubicWires.RepairOrdinary.CloseoutRowsReusableCuts
