import Proof.CaseAnalysis.RowsLoopLayout

/-! The accepted degree pass, four small updates and six metadata copies
return exactly the next pass's boundary, including the append cursor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsLoopBoundary
open LocalBitMultitape CloseoutRowsLoopLayout CloseoutRowsDegreeReset
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def emitted {n : ℕ} (gs : List (ExactThresholdGate n)) (p w j : ℕ)
    (rows : List (List Bool)) := RowTupleCutList.output gs p rows
      (RowTupleSubsets.selected w rows.length (j+1)) ((-2 : ℤ)^j)
noncomputable def advanced {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  CloseoutRowsDegreeNext.output (finalTapes gs p F w j C rows out) w (j+1) j
noncomputable def reloaded {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  CloseoutRowsMetadataReload.data (advanced gs p F w j C rows out) C
    (templates p w rows.length (j+1)) 6

theorem original_outside (i : Fin 49) (j : Fin 6) :
    CloseoutRowsMetadataReload.dest j≠i.castAdd 63 := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  have hd : ∀ k : Fin 6,51≤(CloseoutRowsMetadataReload.dest k).val := by decide
  have hj := hd j
  change (CloseoutRowsMetadataReload.dest j).val=i.val at hv
  omega

theorem work_pick (i : Fin 54) :
    RecoveryFocus.pick CloseoutRowsMetadataReload.dest ((i.natAdd 49).castAdd 9)=
      if i=2 then some 0 else if i=3 then some 1 else if i=12 then some 2
      else if i=17 then some 3 else if i=40 then some 4 else if i=41 then some 5 else none := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot _ CloseoutRowsMetadataReload.dest_injective 0
    | exact RecoveryFocus.pick_slot _ CloseoutRowsMetadataReload.dest_injective 1
    | exact RecoveryFocus.pick_slot _ CloseoutRowsMetadataReload.dest_injective 2
    | exact RecoveryFocus.pick_slot _ CloseoutRowsMetadataReload.dest_injective 3
    | exact RecoveryFocus.pick_slot _ CloseoutRowsMetadataReload.dest_injective 4
    | exact RecoveryFocus.pick_slot _ CloseoutRowsMetadataReload.dest_injective 5
    | decide

theorem pad_nil (C : ℕ) : ZeroPadding.pad C []=List.replicate C false := by simp [ZeroPadding.pad]

theorem native_low {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) (i : Fin 36) :
    reloaded gs p F w j C rows out (i.castAdd 76)=
      inputTapes gs p F w (j+1) C rows (out++emitted gs p w j rows) (i.castAdd 76) := by
  rw [reloaded,CloseoutRowsMetadataReload.data_other _ _ _ _ (i.castAdd 76) (original_outside (i.castAdd 13))]
  have hb := i.isLt
  have h40 : (i.castAdd 76 : Fin 112)≠40 := by intro h; have hv:=congrArg Fin.val h; change i.val=40 at hv; omega
  have h46 : (i.castAdd 76 : Fin 112)≠46 := by intro h; have hv:=congrArg Fin.val h; change i.val=46 at hv; omega
  have h108 : (i.castAdd 76 : Fin 112)≠108 := by intro h; have hv:=congrArg Fin.val h; change i.val=108 at hv; omega
  have h110 : (i.castAdd 76 : Fin 112)≠110 := by intro h; have hv:=congrArg Fin.val h; change i.val=110 at hv; omega
  have h48 : (i.castAdd 53 : Fin 89)≠48 := by intro h; have hv:=congrArg Fin.val h; change i.val=48 at hv; omega
  have hs : selected (i.castAdd 67)=false := by
    apply decide_eq_false
    intro h
    have hv : i.val=44 ∨ i.val=47 ∨ i.val=48 ∨ 49 ≤ i.val := by simpa [Fin.ext_iff] using h
    rcases hv with hv|hv|hv|hv <;> omega
  have left : advanced gs p F w j C rows out (i.castAdd 76)=
      (nativeEnd gs p F w j rows out).tapes (i.castAdd 13) := by
    simp only [advanced,CloseoutRowsDegreeNext.output,CloseoutRowsDegreeNext.nextRaw,
      CloseoutRowsDegreeNext.nextTemplate,CloseoutRowsDegreeNext.nextNative,CloseoutRowsDegreeNext.zeroBound,
      Function.update_of_ne h110,Function.update_of_ne h108,Function.update_of_ne h46,Function.update_of_ne h40]
    change finalTapes gs p F w j C rows out (((i.castAdd 13).castAdd 54).castAdd 9)=_
    have hs' : selected ((i.castAdd 13).castAdd 54)=false := hs
    simp only [finalTapes,Fin.addCases_left,hs',Bool.false_eq_true,↓reduceIte]
  have right : inputTapes gs p F w (j+1) C rows (out++emitted gs p w j rows) (i.castAdd 76)=
      (rawInput gs p F w (j+1) rows (out++emitted gs p w j rows)).tapes (i.castAdd 67) := by
    change inputTapes gs p F w (j+1) C rows (out++emitted gs p w j rows) ((i.castAdd 67).castAdd 9)=_
    simp only [inputTapes,Fin.addCases_left,caps,hs,Bool.false_eq_true,↓reduceIte,ZeroPadding.pad_zero]
  rw [left,right]
  change _=(rawInput gs p F w (j+1) rows (out++emitted gs p w j rows)).tapes ((i.castAdd 53).castAdd 14)
  simp only [rawInput,CloseoutRowsComputedCuts.input,Fin.addCases_left]
  rw [Function.update_of_ne h48]
  change _=(CloseoutRowsEnumeratedCuts.input (0 : Fin 1) gs p F w (j+1+1) rows
    (out++emitted gs p w j rows) ((-2 : ℤ)^(j+1))).tapes ((i.castAdd 13).castAdd 40)
  simp only [CloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,Fin.addCases_left]
  rw [show (i.castAdd 13 : Fin 49)=(i.castAdd 12).castAdd 1 from rfl]
  simp only [nativeEnd,CloseoutRowsEnumeratedCuts.finished,CloseoutRowsEnumeratedCuts.core,
    Fin.addCases_left,RowTupleCursorLayout.data]
  rfl

theorem native_high {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool)
    (h47 : RowTupleCursorReady.capacity gs.length w rows.length (j+2)≤C) (i : Fin 13) :
    reloaded gs p F w j C rows out ((i.natAdd 36).castAdd 63)=
      inputTapes gs p F w (j+1) C rows (out++emitted gs p w j rows) ((i.natAdd 36).castAdd 63) := by
  rw [reloaded,CloseoutRowsMetadataReload.data_other _ _ _ _ _ (original_outside (i.natAdd 36))]
  fin_cases i
  all_goals simp [advanced,CloseoutRowsDegreeNext.output,CloseoutRowsDegreeNext.nextRaw,
    CloseoutRowsDegreeNext.nextTemplate,CloseoutRowsDegreeNext.nextNative,CloseoutRowsDegreeNext.zeroBound,
    finalTapes,inputTapes,rawInput,CloseoutRowsComputedCuts.input,CloseoutRowsComputedCuts.body,
    CloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,nativeEnd,CloseoutRowsEnumeratedCuts.finished,
    CloseoutRowsEnumeratedCuts.core,RowTupleCursorLayout.data,
    RowTupleCursorBody.padding,caps,selected,Fin.addCases,pad_nil,
    Rewind.Workspace.pad_zeros,h47,Nat.add_assoc]

theorem native_next {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool)
    (h47 : RowTupleCursorReady.capacity gs.length w rows.length (j+2)≤C) (i : Fin 49) :
    reloaded gs p F w j C rows out (i.castAdd 63)=
      inputTapes gs p F w (j+1) C rows (out++emitted gs p w j rows) (i.castAdd 63) := by
  refine Fin.addCases (m:=36) (n:=13) (fun a=>?_) (fun a=>?_) i
  · exact native_low gs p F w j C rows out a
  · exact native_high gs p F w j C rows out h47 a

theorem work_next {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) (i : Fin 54) :
    reloaded gs p F w j C rows out ((i.natAdd 49).castAdd 9)=
      inputTapes gs p F w (j+1) C rows (out++emitted gs p w j rows) ((i.natAdd 49).castAdd 9) := by
  simp only [reloaded,CloseoutRowsMetadataReload.data,work_pick]
  fin_cases i
  all_goals simp [advanced,CloseoutRowsDegreeNext.output,CloseoutRowsDegreeNext.nextRaw,
    CloseoutRowsDegreeNext.nextTemplate,CloseoutRowsDegreeNext.nextNative,CloseoutRowsDegreeNext.zeroBound,
    finalTapes,inputTapes,rawInput,CloseoutRowsComputedCuts.input,CloseoutRowsComputedCuts.body,
    CloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,RowTupleEnumeratedEquations.extra,
    CloseoutRowsDegreeCoefficient.input,caps,selected,Fin.addCases,templates,pad_nil,Nat.add_assoc]

end NearCubicWires.RepairOrdinary.CloseoutRowsLoopBoundary
