import Proof.MachineModel.BankFields
import Proof.MachineModel.OrdinaryMatrixBucketRootPower

/-! The actual incidence table and two copies of its last row index are the
only row-dependent native inputs. Common false backing erases the dependence
of the two scratch extents on the number of monomial occurrences. -/
namespace NearCubicWires.ExtIncidence.BankMetadata
open LocalBitMultitape RepairOrdinary
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem last_index {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w C : ℕ)
    (rows : List (List Bool)) (out : List Bool) :
    (CloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes 52=
      ZeroPadding.pad C (frame (SignedSortKey.binary w (rows.length-1))) ∧
    (CloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes 107=
      ZeroPadding.pad C (frame (SignedSortKey.binary w (rows.length-1))) := by
  constructor
  · change ZeroPadding.pad C (ZeroPadding.pad C _) = _
    exact MatrixBucketRootPower.pad_pad C C _ le_rfl
  · rfl

theorem cursor_other {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w M : ℕ)
    (rows : List (List Bool)) (out : List Bool) (i : Fin 48)
    (h36 : i.val≠36) (h43 : i.val≠43) (h47 : i.val≠47) :
    RowTupleCursorLayout.data gs 0 p F w M 1 rows [] out 0 [] i=
      RowTupleCursorLayout.data gs 0 p F w 0 1 [] [] out 0 [] i := by
  revert h36 h43 h47
  refine Fin.addCases (m:=36) (n:=12) (fun j=>?_) (fun j=>?_) i
  · intro _ _ _
    simp only [RowTupleCursorLayout.data,Fin.addCases_left]
  · intro h36 h43 h47
    simp only [RowTupleCursorLayout.data,Fin.addCases_right]
    fin_cases j <;> simp_all

theorem raw_other {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w : ℕ)
    (rows : List (List Bool)) (out : List Bool) (i : Fin 103)
    (h36 : i.val≠36) (h43 : i.val≠43) (h47 : i.val≠47) (h52 : i.val≠52) :
    (CloseoutRowsLoopLayout.rawInput gs p F w 0 rows out).tapes i=
      (CloseoutRowsLoopLayout.rawInput gs p F w 0 [] out).tapes i := by
  revert h36 h43 h47 h52
  refine Fin.addCases (m:=89) (n:=14) (fun a=>?_) (fun a=>?_) i
  · refine Fin.addCases (m:=49) (n:=40) (fun b=>?_) (fun b=>?_) a
    · refine Fin.addCases (m:=48) (n:=1) (fun c=>?_) (fun c=>?_) b
      · intro h36 h43 h47 _
        have hn : ((c.castAdd 1).castAdd 40 : Fin 89)≠48 := by
          intro he
          have hv : c.val=48:=congrArg (fun x : Fin 89=>x.val) he
          exact Nat.ne_of_lt c.isLt hv
        simp only [CloseoutRowsLoopLayout.rawInput,CloseoutRowsComputedCuts.input,
          Fin.addCases_left,Function.update_of_ne hn,CloseoutRowsComputedCuts.body,
          CloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,CloseoutRowsEnumeratedCuts.core]
        apply congrArg
        exact cursor_other gs p F w rows.length rows out c h36 h43 h47
      · intro _ _ _ _
        simp only [CloseoutRowsLoopLayout.rawInput,CloseoutRowsComputedCuts.input,Fin.addCases_left]
        fin_cases c
        change Function.update (CloseoutRowsComputedCuts.body (0 : Fin 1) gs p F w 0 rows out).tapes (48 : Fin 89) [] 48=
          Function.update (CloseoutRowsComputedCuts.body (0 : Fin 1) gs p F w 0 [] out).tapes (48 : Fin 89) [] 48
        simp only [Function.update_self]
    · intro _ _ _ h52
      have hn : (b.natAdd 49 : Fin 89)≠48 := by
        intro he
        have hv : 49+b.val=48:=congrArg (fun x : Fin 89=>x.val) he
        omega
      simp only [CloseoutRowsLoopLayout.rawInput,CloseoutRowsComputedCuts.input,
        Fin.addCases_left,Function.update_of_ne hn,CloseoutRowsComputedCuts.body,
        CloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,Fin.addCases_right]
      have h3 : b≠3 := by intro he;subst b;exact h52 rfl
      simp only [RowTupleEnumeratedEquations.extra,h3,↓reduceIte]
  · intro _ _ _ _
    simp only [CloseoutRowsLoopLayout.rawInput,CloseoutRowsComputedCuts.input,Fin.addCases_right]

theorem other {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w C : ℕ)
    (rows : List (List Bool)) (out : List Bool) (i : Fin 113)
    (h36 : i.val≠36) (h43 : i.val≠43) (h47 : i.val≠47)
    (h52 : i.val≠52) (h107 : i.val≠107) :
    (CloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes i=
      (CloseoutRowsBankPolynomial.entry gs p F Q w C [] out).tapes i := by
  apply congrArg (ZeroPadding.pad (CloseoutRowsBankCapacity.capacities C i))
  simp only [CloseoutRowsPolynomial.input,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    CloseoutRowsDegreeLoop.entry]
  revert h36 h43 h47 h52 h107
  refine Fin.addCases (m:=112) (n:=1) (fun a=>?_) (fun a=>?_) i
  · refine Fin.addCases (m:=103) (n:=9) (fun b=>?_) (fun b=>?_) a
    · intro h36 h43 h47 h52 _
      simp only [Fin.addCases_left,CloseoutRowsLoopLayout.inputTapes]
      apply congrArg
      exact raw_other gs p F w rows out b h36 h43 h47 h52
    · intro _ _ _ _ h107
      simp only [Fin.addCases_left,CloseoutRowsLoopLayout.inputTapes,Fin.addCases_right,
        CloseoutRowsLoopLayout.extra,CloseoutRowsLoopLayout.templates]
      fin_cases b <;> simp_all [Fin.addCases]
  · intro _ _ _ _ _
    simp only [Fin.addCases_right]

theorem false_backing (C k : ℕ) (hk : k≤C) :
    ZeroPadding.pad C (List.replicate k false)=List.replicate C false := by
  simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add,Nat.add_sub_of_le hk]

theorem scratch {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w : ℕ)
    (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hw : rows.length≤2^w)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    let C:=CloseoutRowsPreparationBounds.capacity n p F w gs.length Q
    (CloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes 43=List.replicate C false ∧
    (CloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes 47=List.replicate C false := by
  dsimp only
  let C:=CloseoutRowsPreparationBounds.capacity n p F w gs.length Q
  have b43:=CloseoutRowsBankCapacity.raw_bound gs p F Q w 0 rows out hl hw (Nat.zero_le Q) hF 43 (by decide)
  have b47:=CloseoutRowsBankCapacity.raw_bound gs p F Q w 0 rows out hl hw (Nat.zero_le Q) hF 47 (by decide)
  change (ZeroPadding.pad 0 (List.replicate (RowMaskLookupReusable.capacity gs.length w rows.length) false)).length≤C at b43
  change (ZeroPadding.pad 0 (List.replicate (RowTupleCursorReady.capacity gs.length w rows.length 1) false)).length≤C at b47
  rw [ZeroPadding.pad_zero,List.length_replicate] at b43 b47
  constructor
  · change ZeroPadding.pad C (ZeroPadding.pad 0 (ZeroPadding.pad 0
      (List.replicate (RowMaskLookupReusable.capacity gs.length w rows.length) false)))=_
    rw [ZeroPadding.pad_zero,ZeroPadding.pad_zero]
    exact false_backing C _ b43
  · change ZeroPadding.pad C (ZeroPadding.pad C (ZeroPadding.pad 0
      (List.replicate (RowTupleCursorReady.capacity gs.length w rows.length 1) false)))=_
    rw [ZeroPadding.pad_zero,MatrixBucketRootPower.pad_pad C C _ le_rfl]
    exact false_backing C _ b47

theorem row_independent {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w : ℕ)
    (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hw : rows.length≤2^w)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F)
    (i : Fin 113) (h36 : i≠36) (h52 : i≠52) (h107 : i≠107) :
    let C:=CloseoutRowsPreparationBounds.capacity n p F w gs.length Q
    (CloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes i=
      (CloseoutRowsBankPolynomial.entry gs p F Q w C [] out).tapes i := by
  dsimp only
  by_cases h43 : i=43
  · subst i
    exact (scratch gs p F Q w rows out hl hw hF).1.trans
      (scratch gs p F Q w [] out (by simp) (by simp) hF).1.symm
  by_cases h47 : i=47
  · subst i
    exact (scratch gs p F Q w rows out hl hw hF).2.trans
      (scratch gs p F Q w [] out (by simp) (by simp) hF).2.symm
  exact other gs p F Q w _ rows out i
    (fun h=>h36 (Fin.ext h)) (fun h=>h43 (Fin.ext h)) (fun h=>h47 (Fin.ext h))
    (fun h=>h52 (Fin.ext h)) (fun h=>h107 (Fin.ext h))

end NearCubicWires.ExtIncidence.BankMetadata
