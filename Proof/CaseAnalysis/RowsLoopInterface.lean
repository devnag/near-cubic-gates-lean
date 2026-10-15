import Proof.CaseAnalysis.RowsLoopBoundary

/-! The full next-call identity and actual metadata inputs at the shared
degree boundary. Every source and cursor is inherited from one receipt. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsLoopInterface
open LocalBitMultitape CloseoutRowsLoopLayout CloseoutRowsLoopBoundary CloseoutRowsDegreeReset
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem extra_outside (i : Fin 9) (j : Fin 6) :
    CloseoutRowsMetadataReload.dest j≠i.natAdd 103 := by
  intro h
  have hv := congrArg Fin.val h
  have hd : ∀ k : Fin 6,(CloseoutRowsMetadataReload.dest k).val≤90 := by decide
  have hj := hd j
  change (CloseoutRowsMetadataReload.dest j).val=103+i.val at hv
  omega

theorem extra_next {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) (i : Fin 9) :
    reloaded gs p F w j C rows out (i.natAdd 103)=
      inputTapes gs p F w (j+1) C rows (out++emitted gs p w j rows) (i.natAdd 103) := by
  rw [reloaded,CloseoutRowsMetadataReload.data_other _ _ _ _ _ (extra_outside i)]
  fin_cases i
  all_goals simp [advanced,CloseoutRowsDegreeNext.output,CloseoutRowsDegreeNext.nextRaw,
    CloseoutRowsDegreeNext.nextTemplate,CloseoutRowsDegreeNext.nextNative,CloseoutRowsDegreeNext.zeroBound,
    finalTapes,inputTapes,extra,templates,Fin.addCases,Nat.add_assoc]

theorem all_tapes {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool)
    (h47 : RowTupleCursorReady.capacity gs.length w rows.length (j+2)≤C) :
    reloaded gs p F w j C rows out=
      inputTapes gs p F w (j+1) C rows (out++emitted gs p w j rows) := by
  funext i
  refine Fin.addCases (m:=103) (n:=9) (fun a=>?_) (fun a=>?_) i
  · refine Fin.addCases (m:=49) (n:=54) (fun b=>?_) (fun b=>?_) a
    · exact native_next gs p F w j C rows out h47 b
    · exact work_next gs p F w j C rows out b
  · exact extra_next gs p F w j C rows out a

theorem all_heads {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) :
    finalHeads gs p F w j rows out=
      inputHeads gs p F w (j+1) rows (out++emitted gs p w j rows) := by
  funext i
  refine Fin.addCases (m:=103) (n:=9) (fun a=>?_) (fun a=>?_) i
  · refine Fin.addCases (m:=49) (n:=54) (fun b=>?_) (fun b=>?_) a
    · fin_cases b
      all_goals simp [finalHeads,inputHeads,rawInput,CloseoutRowsComputedCuts.input,
        CloseoutRowsComputedCuts.body,CloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,
        nativeEnd,CloseoutRowsEnumeratedCuts.finished,CloseoutRowsEnumeratedCuts.core,
        RowTupleCursorLayout.heads,selected,Fin.addCases,emitted]
    · fin_cases b <;> rfl
  · fin_cases a <;> rfl

theorem initial_reload {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) :
    CloseoutRowsMetadataReload.data (advanced gs p F w j C rows out) C
      (templates p w rows.length (j+1)) 0=advanced gs p F w j C rows out := by
  funext i
  cases hp : RecoveryFocus.pick CloseoutRowsMetadataReload.dest i with
  | none=>simp only [CloseoutRowsMetadataReload.data,hp]
  | some k=>
    have hi := RecoveryFocus.slot_of_pick CloseoutRowsMetadataReload.dest hp
    simp only [CloseoutRowsMetadataReload.data,hp,Nat.not_lt_zero,↓reduceIte]
    rw [←hi]
    fin_cases k <;> rfl

theorem metadata_fields {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) :
    (∀ i,advanced gs p F w j C rows out (CloseoutRowsMetadataReload.source i)=templates p w rows.length (j+1) i) ∧
      advanced gs p F w j C rows out 104=List.replicate C true ∧
      advanced gs p F w j C rows out 105=List.replicate (C+1) false ∧
      (∀ i k,finalHeads gs p F w j rows out (CloseoutRowsMetadataReload.slots i k)=0) := by
  refine ⟨?_,rfl,rfl,?_⟩
  · intro i
    fin_cases i <;> rfl
  · intro i k
    fin_cases i <;> fin_cases k <;> rfl

theorem templates_bound (p w M j C : ℕ) (hc : 2*w+p+j+3≤C) :
    ∀ i,(templates p w M (j+1) i).length≤C := by
  intro i
  fin_cases i <;> simp [templates,CompareMachine.word,frame_length,SignedSortKey.binary_length] <;> omega

theorem advance_fields {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) :
    finalTapes gs p F w j C rows out 39=frame (SignedSortKey.binary w 0) ∧
      finalTapes gs p F w j C rows out 40=frame (SignedSortKey.binary w
        (RowTupleCutList.finalBound rows (RowTupleSubsets.selected w rows.length (j+1)) 0)) ∧
      finalTapes gs p F w j C rows out 46=CompareMachine.word (j+1) ∧
      finalTapes gs p F w j C rows out 108=CompareMachine.word (j+1) ∧
      finalTapes gs p F w j C rows out 110=List.replicate j true ∧
      finalTapes gs p F w j C rows out 103=List.replicate C false ∧
      finalTapes gs p F w j C rows out 105=List.replicate (C+1) false ∧
      (∀ i,finalHeads gs p F w j rows out (CloseoutRowsDegreeNext.frameSlots i)=0) ∧
      finalHeads gs p F w j rows out 46=1 ∧
      finalHeads gs p F w j rows out 108=0 ∧ finalHeads gs p F w j rows out 110=0 := by
  refine ⟨?_,?_,?_,rfl,rfl,rfl,rfl,?_,rfl,rfl,rfl⟩
  · simp [finalTapes,nativeEnd,CloseoutRowsEnumeratedCuts.finished,CloseoutRowsEnumeratedCuts.core,
      selected,RowTupleCursorLayout.data,RowTupleCursorBody.padding,Fin.addCases]
  · simp [finalTapes,nativeEnd,CloseoutRowsEnumeratedCuts.finished,CloseoutRowsEnumeratedCuts.core,
      selected,RowTupleCursorLayout.data,RowTupleCursorBody.padding,Fin.addCases]
  · simp [finalTapes,nativeEnd,CloseoutRowsEnumeratedCuts.finished,CloseoutRowsEnumeratedCuts.core,
      selected,RowTupleCursorLayout.data,RowTupleCursorBody.padding,Fin.addCases]
  · intro i
    fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsLoopInterface
