import Proof.CaseAnalysis.RowsBankClear

/-! A complete polynomial call returns to the enclosing bank's erased
native ports. Every transition and sweep is paid; the growing output stays live. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsBankPolynomial
open LocalBitMultitape CloseoutRowsLoopLayout CloseoutRowsLoopBoundary
open CloseoutRowsPreparationBounds CloseoutRowsPreparationFits CloseoutRowsPreparationInput
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  ZeroPadding.config (CloseoutRowsBankCapacity.capacities C)
    (CloseoutRowsPolynomial.input gs p F Q w C rows out)

theorem padded_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (p F Q w : ℕ) (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length)
    (hw : rows.length<2^w) (hQp : Q ≤ p)
    (hp : RowTupleFixedCapacity.width gs Q ≤ p)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p ≤ F) :
    let C:=capacity (l+r) p F w gs.length Q
    let word:=out++(CloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p)
    ∃ actual,runFrom CloseoutRowsPolynomial.machine (CloseoutRowsDegreeLoop.budget Q C)
      (input gs p F Q w C rows out)=some actual ∧
      actual.final.heads=CloseoutRowsBankFields.heads word ∧ actual.final.tapes 31=word ∧
      actual.final.tapes 104=List.replicate C true ∧ actual.final.tapes 105=List.replicate (C+1) false ∧
      (∀ i,i≠31 → i≠105 → (actual.final.tapes i).length ≤ C) ∧
      actual.steps ≤ CloseoutRowsDegreeLoop.budget Q C := by
  dsimp only
  let C:=capacity (l+r) p F w gs.length Q
  have hcopy : 4*w+3 ≤ C := by
    have h:=small_fits (l+r) p F w gs.length Q
    unfold scale at h
    dsimp only [C]
    omega
  obtain ⟨source,hs,sf,ss⟩ := CloseoutRowsDegreeLoop.degrees_run gs p F Q w C rows out hl hM hw hQp hp hF
    (fun j hj=>computed_fits gs p F Q w j rows hl hw.le hj)
    (fun j hj=>selected_fits gs p F Q w j rows hw.le hj) hcopy
    (fun j hj=>(metadata_fits (l+r) p F w gs.length Q j hj).2)
    (fun j hj=>cursor_fits (l+r) p F w gs.length Q rows.length (j+2) hw.le (by omega))
  obtain ⟨actual,ha,af,asteps,_⟩ := ZeroPadding.run_config CloseoutRowsPolynomial.machine
    (CloseoutRowsBankCapacity.capacities C) _ _ source hs
  have hout := CloseoutRowsSharedDigits.emitted_word gs p Q w rows
  have he : (List.range Q).flatMap (fun j=>emitted gs p w j rows)=
      (CloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p) := hout
  rw [he] at sf
  refine ⟨actual,ha,?_,?_,?_,?_,?_,asteps.le.trans ss⟩
  · rw [af,sf]
    exact CloseoutRowsBankCapacity.loop_heads _ gs 3 p F Q w Q C rows _
  · rw [af,sf]
    change ZeroPadding.pad 0 (inputTapes gs p F w Q C rows _ 31)=_
    rw [ZeroPadding.pad_zero,(CloseoutRowsPolynomial.output_fields gs p F w Q C rows _).1]
  · rw [af,sf]
    change ZeroPadding.pad C (List.replicate C true)=_
    simp [ZeroPadding.pad,C]
  · rw [af,sf]
    change ZeroPadding.pad (C+1) (List.replicate (C+1) false)=_
    simp [ZeroPadding.pad,C]
  · intro i hi hlog
    rw [af,sf]
    change (ZeroPadding.pad (CloseoutRowsBankCapacity.capacities C i) _).length ≤ C
    rw [ZeroPadding.pad_length]
    apply max_le
    · simp only [CloseoutRowsBankCapacity.capacities,hi,hlog,↓reduceIte,le_refl]
    · exact CloseoutRowsBankCapacity.loop_bound _ gs 3 p F Q w Q rows _ hl hw.le le_rfl hF i hi hlog

noncomputable def machine := Composition.machine CloseoutRowsPolynomial.machine CloseoutRowsBankClear.machine
def budget (Q C : ℕ) := CloseoutRowsDegreeLoop.budget Q C+1+CloseoutRowsBankClear.budget C
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  Composition.leftConfig 6 (input gs p F Q w C rows out)

theorem polynomial_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (p F Q w : ℕ) (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length)
    (hw : rows.length<2^w) (hQp : Q ≤ p)
    (hp : RowTupleFixedCapacity.width gs Q ≤ p)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p ≤ F) :
    let C:=capacity (l+r) p F w gs.length Q
    let word:=out++(CloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p)
    ∃ actual,runFrom machine (budget Q C) (entry gs p F Q w C rows out)=some actual ∧
      actual.final.heads=CloseoutRowsBankClear.zeroHeads word ∧ actual.final.tapes 31=word ∧
      (∀ i,actual.final.tapes (CloseoutRowsBankClear.slots i)=CloseoutRowsBankClear.erased C i) ∧
      actual.steps ≤ budget Q C := by
  dsimp only
  let C:=capacity (l+r) p F w gs.length Q
  let word:=out++(CloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p)
  obtain ⟨a,ha,ah,aout,ad,al,ab,_⟩ := padded_run gs p F Q w rows out hl hM hw hQp hp hF
  obtain ⟨b,hb,bh,bt,bout,_⟩ := CloseoutRowsBankClear.clear_run C word a.final.tapes ab ad al
  have he : Composition.restart a.final CloseoutRowsBankClear.machine.start=
      ⟨CloseoutRowsBankClear.machine.start,CloseoutRowsBankFields.heads word,a.final.tapes⟩ := by
    apply configuration_ext
    · rfl
    · exact ah
    · rfl
  rw [←he] at hb
  have whole := Composition.run_join CloseoutRowsPolynomial.machine CloseoutRowsBankClear.machine _ _ _ a b ha hb
  exact ⟨Composition.joinedReceipt a b,whole,bh,bout.trans aout,bt,runFrom_steps_le machine _ _ _ whole⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsBankPolynomial
