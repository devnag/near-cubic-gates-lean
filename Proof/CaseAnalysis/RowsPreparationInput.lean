import Proof.CaseAnalysis.RowsPreparationFits

/-! The concrete shared preparation capacity discharges the actual native
metadata and every selected initial work-tape extent. The growing output
prefix is absent from all of these bounds. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPreparationInput
open CloseoutRowsPreparationBounds CloseoutRowsPreparationFits
open LocalBitMultitape CloseoutRowsLoopLayout
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem small_fits (n p F w N Q : ℕ) :
    16*scale n p F w N Q ≤ capacity n p F w N Q := by
  have hS := (scale_fields n p F w N Q).1
  have hpow : scale n p F w N Q ≤ (scale n p F w N Q)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hS (show 1 ≤ 4 by decide)
  have he : 1 ≤ 2^(w*(Q+1)) := Nat.one_le_two_pow
  unfold capacity
  nlinarith [Nat.mul_le_mul_right ((scale n p F w N Q)^4) he]

theorem metadata_fits (n p F w N Q j : ℕ) (hj : j<Q) :
    4*w+3 ≤ capacity n p F w N Q ∧ 2*w+p+j+3 ≤ capacity n p F w N Q := by
  have h := small_fits n p F w N Q
  unfold scale at h
  omega

theorem native_fits {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w j : ℕ) (rows : List (List Bool)) (hM : rows.length ≤ 2^w) (hj : j<Q)
    (out : List Bool) (i : Fin 49) (hi : CloseoutRowsDegreeReset.selected (i.castAdd 54)=true) :
    ((rawInput gs p F w j rows out).tapes (i.castAdd 54)).length ≤ capacity n p F w gs.length Q := by
  have hc := cursor_fits n p F w gs.length Q rows.length (j+1) hM (by omega)
  have hm := (metadata_fits n p F w gs.length Q j hj).2
  have h : i.val=44 ∨ i.val=47 ∨ i.val=48 ∨ 49 ≤ i.val := by
    simpa [CloseoutRowsDegreeReset.selected,Fin.ext_iff] using hi
  rcases h with h | h | h | h
  · have he : i=44 := Fin.ext h
    subst i
    simp [rawInput,CloseoutRowsComputedCuts.input,CloseoutRowsComputedCuts.body,
      CloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,CloseoutRowsEnumeratedCuts.core,
      RowTupleCursorBody.padding,RowTupleCursorLayout.data,Fin.addCases,ZeroPadding.pad]
  · have he : i=47 := Fin.ext h
    subst i
    simpa [rawInput,CloseoutRowsComputedCuts.input,CloseoutRowsComputedCuts.body,
      CloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,CloseoutRowsEnumeratedCuts.core,
      RowTupleCursorBody.padding,RowTupleCursorLayout.data,Fin.addCases,ZeroPadding.pad] using hc
  · have he : i=48 := Fin.ext h
    subst i
    simp [rawInput,CloseoutRowsComputedCuts.input,Fin.addCases]
  · have hb:=i.isLt
    omega

theorem enum_fits {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w j : ℕ) (rows : List (List Bool)) (hj : j<Q)
    (out : List Bool) (i : Fin 40) :
    ((rawInput gs p F w j rows out).tapes ((i.natAdd 49).castAdd 14)).length ≤ capacity n p F w gs.length Q := by
  have hm := (metadata_fits n p F w gs.length Q j hj).2
  have hi : (i.natAdd 49 : Fin 89)≠48 := by
    intro h
    have hv:=congrArg Fin.val h
    change 49+i.val=48 at hv
    omega
  simp only [rawInput,CloseoutRowsComputedCuts.input,Fin.addCases_left,Function.update_of_ne hi,
    CloseoutRowsComputedCuts.body,CloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,Fin.addCases_right]
  simp only [RowTupleEnumeratedEquations.extra]
  split_ifs <;> simp [CompareMachine.word,frame_length,SignedSortKey.binary_length] <;> omega

theorem coefficient_fits {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w j : ℕ) (rows : List (List Bool)) (hj : j<Q)
    (out : List Bool) (i : Fin 14) :
    ((rawInput gs p F w j rows out).tapes (i.natAdd 89)).length ≤ capacity n p F w gs.length Q := by
  have hm := (metadata_fits n p F w gs.length Q j hj).2
  simp only [rawInput,CloseoutRowsComputedCuts.input,Fin.addCases_right]
  fin_cases i <;> simp [CloseoutRowsDegreeCoefficient.input] <;> omega

theorem selected_fits {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w j : ℕ) (rows : List (List Bool)) (hM : rows.length ≤ 2^w) (hj : j<Q) :
    ∀ out i,CloseoutRowsDegreeReset.selected i=true →
      ((rawInput gs p F w j rows out).tapes i).length ≤ capacity n p F w gs.length Q := by
  intro out i
  refine Fin.addCases (m:=89) (n:=14) (fun a=>?_) (fun a=>?_) i
  · refine Fin.addCases (m:=49) (n:=40) (fun b=>?_) (fun b=>?_) a
    · exact native_fits gs p F Q w j rows hM hj out b
    · intro _
      exact enum_fits gs p F Q w j rows hj out b
  · intro _
    exact coefficient_fits gs p F Q w j rows hj out a

end NearCubicWires.RepairOrdinary.CloseoutRowsPreparationInput
