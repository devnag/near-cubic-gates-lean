import Proof.Hierarchy.CompetitorMonomialWidthFields

/-! The native monomial caller is prepared from a canonical coefficient,
count and normalization-denominator record. Both global cursors survive the
physical scratch clear and runtime-width preparation. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision CompetitorMonomialProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Store (b t : ℕ) (source output : List Bool) (ambient : Fin 88 → List Bool) : Prop where
  source : ambient 79=source
  output : ambient 74=output
  inputWidth : ambient 81=List.replicate (width b) true
  targetWidth : ambient 82=List.replicate (width t) true
  shortWidth : ambient 83=List.replicate t true
  eraseDriver : ambient 84=List.replicate (capacity t) true
  eraseReset : ambient 85=List.replicate (capacity t+1) false
  support : ∀ j,(ambient (workSlot j)).length≤capacity t

def allWidths : List (Fin 3) := [0,1,2]
def allFields : List (Fin 6) := [0,1,2,3,4,5]
def recordFields (b : ℕ) (q : ℚ) (count denominator : ℕ) : Fin 6 → List Bool :=
  ![binary (width b) (positive q),binary (width b) (negative q),binary (width b) q.den,
    binary (width b) 0,binary b denominator,binary b count]
def recordWord (b : ℕ) (q : ℚ) (count denominator : ℕ) := fieldStream (recordFields b q count denominator) allFields
noncomputable def clean (t : ℕ) (ambient : Fin 88 → List Bool) := cleared (capacity t) workSlot ambient
noncomputable def widened (b t : ℕ) (ambient : Fin 88 → List Bool) := widthPlaced b t allWidths (clean t ambient)
noncomputable def prepared (b t : ℕ) (q : ℚ) (count denominator : ℕ) (ambient : Fin 88 → List Bool) :=
  placed t (recordFields b q count denominator) allFields (widened b t ambient)
noncomputable def widthPrepareProgram := Composition.machine (clearProgram workSlot) (widthsProgram allWidths)
noncomputable def prepareProgram := Composition.machine widthPrepareProgram (fieldsProgram allFields)
def widthPrepareBudget (b t : ℕ) := 2*capacity t+5+widthCost b t allWidths
def prepareBudget (b t : ℕ) := widthPrepareBudget b t+1+40*b+56

theorem clear_keep (t : ℕ) (ambient : Fin 88 → List Bool) (i : Fin 88)
    (hi : i=74 ∨ i=79 ∨ i=81 ∨ i=82 ∨ i=83 ∨ i=84 ∨ i=85) : clean t ambient i=ambient i := by
  simp only [clean,cleared,show ¬∃ j,workSlot j=i from fun ⟨j,hj⟩ => work_avoids j i hi hj,if_false]
theorem clear_cell (t : ℕ) (ambient : Fin 88 → List Bool) (i : Fin 88)
    (hi : i.val<79 ∧ i≠74 ∨ i=80 ∨ i=86 ∨ i=87) : clean t ambient i=List.replicate (capacity t) false := by
  simp only [clean,cleared,work_image i hi,if_true]

theorem widened_cases (b t : ℕ) (ambient : Fin 88 → List Bool) (i : Fin 88) :
    widened b t ambient i=
      if i.val=75 then ZeroPadding.pad (capacity t) (List.replicate t true)
      else if i.val=67 then ZeroPadding.pad (capacity t) (List.replicate (width t) true)
      else if i.val=6 then ZeroPadding.pad (capacity t) (List.replicate (width b) true)
      else clean t ambient i := by
  simp [widened,widthPlaced,allWidths,widthLoaded,widthTarget,widths,Function.update_apply,Fin.ext_iff]

theorem prepared_cases (b t : ℕ) (q : ℚ) (count denominator : ℕ) (ambient : Fin 88 → List Bool) (i : Fin 88) :
    prepared b t q count denominator ambient i=
      if i.val=5 then ZeroPadding.pad (capacity t) (frame (binary b count))
      else if i.val=4 then ZeroPadding.pad (capacity t) (frame (binary b denominator))
      else if i.val=3 then ZeroPadding.pad (capacity t) (frame (binary (width b) 0))
      else if i.val=2 then ZeroPadding.pad (capacity t) (frame (binary (width b) q.den))
      else if i.val=1 then ZeroPadding.pad (capacity t) (frame (binary (width b) (negative q)))
      else if i.val=0 then ZeroPadding.pad (capacity t) (frame (binary (width b) (positive q)))
      else widened b t ambient i := by
  simp only [prepared,allFields,placed,loaded,Function.update_apply,target,Fin.ext_iff]
  rfl

theorem prepared_keep (b t : ℕ) (q : ℚ) (count denominator : ℕ) (ambient : Fin 88 → List Bool)
    (i : Fin 88) (hi : i=74 ∨ i=79 ∨ i=81 ∨ i=82 ∨ i=83 ∨ i=84 ∨ i=85) :
    prepared b t q count denominator ambient i=ambient i := by
  rw [prepared_cases,widened_cases]
  have hv : i.val=74 ∨ i.val=79 ∨ i.val=81 ∨ i.val=82 ∨ i.val=83 ∨ i.val=84 ∨ i.val=85 := by
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  simp only [show i.val≠5 by omega,show i.val≠4 by omega,show i.val≠3 by omega,
    show i.val≠2 by omega,show i.val≠1 by omega,show i.val≠0 by omega,
    show i.val≠75 by omega,show i.val≠67 by omega,show i.val≠6 by omega,if_false]
  exact clear_keep t ambient i hi

theorem record_length (b : ℕ) (q : ℚ) (count denominator : ℕ) :
    (recordWord b q count denominator).length=20*b+22 := by
  simp [recordWord,fieldStream,allFields,recordFields,width]
  omega
theorem record_cost (b : ℕ) (q : ℚ) (count denominator : ℕ) :
    fieldCost (recordFields b q count denominator) allFields=40*b+56 := by
  simp [fieldCost,allFields,recordFields,width]
  omega

theorem width_prepare_run (b t outPos pos : ℕ) (source output : List Bool) (ambient : Fin 88 → List Bool)
    (h : Store b t source output ambient) (hbt : b≤t) :
    ∃ r,runFrom widthPrepareProgram (widthPrepareBudget b t)
        (cfg outPos widthPrepareProgram.start pos ambient)=some r ∧
      r.steps≤widthPrepareBudget b t ∧ r.final.heads=heads outPos pos ∧ r.final.tapes=widened b t ambient := by
  obtain ⟨first,hfirst,hfh,hft,hfs⟩ := clear_run workSlot work_injective
    (fun j => work_avoids j 74 (by simp)) (fun j => work_avoids j 79 (by simp))
    (fun j => work_avoids j 84 (by simp)) (fun j => work_avoids j 85 (by simp))
    (capacity t) outPos pos ambient h.eraseDriver h.eraseReset h.support
  have hs : ∀ j∈allWidths,clean t ambient (widthSource j)=List.replicate (widths b t j) true := by
    intro j _
    fin_cases j
    · exact (clear_keep t ambient 81 (by simp)).trans h.inputWidth
    · exact (clear_keep t ambient 82 (by simp)).trans h.targetWidth
    · exact (clear_keep t ambient 83 (by simp)).trans h.shortWidth
  have ht : ∀ j∈allWidths,clean t ambient (widthTarget j)=List.replicate (capacity t) false := by
    intro j _
    apply clear_cell
    fin_cases j <;> decide
  have hw : ∀ j∈allWidths,widths b t j+2≤capacity t := by
    intro j _
    fin_cases j <;> simp [widths,width,capacity] <;> nlinarith
  obtain ⟨last,hlast,hls,hlh,hlt⟩ := widths_run b t outPos pos allWidths (by decide) (clean t ambient)
    hs ht (clear_cell _ _ 86 (by simp)) (clear_cell _ _ 87 (by simp)) hw
  have he : Composition.restart first.final (widthsProgram allWidths).start=
      cfg outPos (widthsProgram allWidths).start pos (clean t ambient) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hl' : runFrom (widthsProgram allWidths) (widthCost b t allWidths)
      (Composition.restart first.final (widthsProgram allWidths).start)=some last := by rw [he]; exact hlast
  have hall := Composition.run_join (clearProgram workSlot) (widthsProgram allWidths) _ _ _ first last hfirst hl'
  have htime : (2*capacity t+4)+1+widthCost b t allWidths=widthPrepareBudget b t := by unfold widthPrepareBudget; omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt first last,hall,?_,hlh,hlt⟩
  change first.steps+1+last.steps≤widthPrepareBudget b t
  omega

theorem prepare_run (b t : ℕ) (q : ℚ) (count denominator : ℕ) (pre suffix output : List Bool)
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

end NearCubicWires.RepairOrdinary.CompetitorMonomialStream
