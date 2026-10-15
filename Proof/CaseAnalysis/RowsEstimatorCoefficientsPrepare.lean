import Proof.CaseAnalysis.RowsEstimatorCoefficientsProducts
import Proof.Hierarchy.CompetitorMonomialPrepare

/-! The existing six-field stream reader, scratch clear, and runtime-width
preparation applied to an unreduced signed coefficient. Physical inputs and
logical cursors are unchanged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision CompetitorMonomialStream
open Products
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def recordFields (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) : Fin 6 → List Bool :=
  ![binary (width b) (q.positive),binary (width b) (q.negative),binary (width b) q.denominator,
    binary (width b) 0,binary b denominator,binary b count]
def recordWord (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) := fieldStream (recordFields b q count denominator) allFields

noncomputable def prepared (b t : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) (ambient : Fin 88 → List Bool) :=
  placed t (recordFields b q count denominator) allFields (widened b t ambient)

theorem prepared_cases (b t : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) (ambient : Fin 88 → List Bool) (i : Fin 88) :
    prepared b t q count denominator ambient i=
      if i.val=5 then ZeroPadding.pad (capacity t) (frame (binary b count))
      else if i.val=4 then ZeroPadding.pad (capacity t) (frame (binary b denominator))
      else if i.val=3 then ZeroPadding.pad (capacity t) (frame (binary (width b) 0))
      else if i.val=2 then ZeroPadding.pad (capacity t) (frame (binary (width b) q.denominator))
      else if i.val=1 then ZeroPadding.pad (capacity t) (frame (binary (width b) (q.negative)))
      else if i.val=0 then ZeroPadding.pad (capacity t) (frame (binary (width b) (q.positive)))
      else widened b t ambient i := by
  simp only [prepared,allFields,placed,loaded,Function.update_apply,target,Fin.ext_iff]
  rfl

theorem prepared_keep (b t : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) (ambient : Fin 88 → List Bool)
    (i : Fin 88) (hi : i=74 ∨ i=79 ∨ i=81 ∨ i=82 ∨ i=83 ∨ i=84 ∨ i=85) :
    prepared b t q count denominator ambient i=ambient i := by
  rw [prepared_cases,widened_cases]
  have hv : i.val=74 ∨ i.val=79 ∨ i.val=81 ∨ i.val=82 ∨ i.val=83 ∨ i.val=84 ∨ i.val=85 := by
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  simp only [show i.val≠5 by omega,show i.val≠4 by omega,show i.val≠3 by omega,
    show i.val≠2 by omega,show i.val≠1 by omega,show i.val≠0 by omega,
    show i.val≠75 by omega,show i.val≠67 by omega,show i.val≠6 by omega,if_false]
  exact clear_keep t ambient i hi

theorem record_length (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) :
    (recordWord b q count denominator).length=20*b+22 := by
  simp [recordWord,fieldStream,allFields,recordFields,width]
  omega
theorem record_cost (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) :
    fieldCost (recordFields b q count denominator) allFields=40*b+56 := by
  simp [fieldCost,allFields,recordFields,width]
  omega

theorem prepare_run (b t : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) (pre suffix output : List Bool)
    (ambient : Fin 88 → List Bool)
    (h : Store b t (pre++recordWord b q count denominator++suffix) output ambient) (hbt : b≤t) :
    ∃ r,runFrom prepareProgram (prepareBudget b t)
        (cfg output.length prepareProgram.start pre.length ambient)=some r ∧
      r.steps≤prepareBudget b t ∧ r.final.heads=heads output.length (pre.length+(recordWord b q count denominator).length) ∧
      r.final.tapes=prepared b t q count denominator ambient := by
  obtain ⟨first,hfirst,hfs,hfh,hft⟩ := width_prepare_run b t output.length pre.length _ _ ambient h hbt
  have hs : widened b t ambient 79=pre++fieldStream (recordFields b q count denominator) allFields++suffix := by
    rw [widened_cases]
    exact (clear_keep t ambient 79 (by simp)).trans h.source
  have ht : ∀ j∈allFields,widened b t ambient (target j)=List.replicate (capacity t) false := by
    intro j _
    rw [widened_cases]
    have hj : (target j).val<6 := j.isLt
    simp only [show (target j).val≠75 by omega,show (target j).val≠67 by omega,
      show (target j).val≠6 by omega,if_false]
    apply clear_cell
    left
    exact ⟨by omega,by intro he; have hv:=congrArg Fin.val he; change j.val=74 at hv; omega⟩
  have hc : widened b t ambient 80=List.replicate (capacity t) false := by
    rw [widened_cases]
    exact clear_cell t ambient 80 (by simp)
  have hcap : ∀ j∈allFields,2*(recordFields b q count denominator j).length+1≤capacity t := by
    intro j _
    fin_cases j <;> simp [recordFields,width,capacity] <;> nlinarith
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := fields_run t output.length (recordFields b q count denominator) allFields
    (by decide) pre suffix (widened b t ambient) hs ht hc hcap
  have he : Composition.restart first.final (fieldsProgram allFields).start=
      cfg output.length (fieldsProgram allFields).start pre.length (widened b t ambient) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hl' : runFrom (fieldsProgram allFields) (fieldCost (recordFields b q count denominator) allFields)
      (Composition.restart first.final (fieldsProgram allFields).start)=some last := by rw [he]; exact hlast
  have hall := Composition.run_join widthPrepareProgram (fieldsProgram allFields) _ _ _ first last hfirst hl'
  have htime : widthPrepareBudget b t+1+fieldCost (recordFields b q count denominator) allFields=prepareBudget b t := by
    rw [record_cost]
    unfold prepareBudget
    omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt first last,hall,?_,hlh,hlt⟩
  change first.steps+1+last.steps≤prepareBudget b t
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream
