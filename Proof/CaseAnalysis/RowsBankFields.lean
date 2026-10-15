import Proof.CaseAnalysis.RowsCapacityBudget
import Proof.CaseAnalysis.RowsRawLoad

/-! The enclosing family controller has one fixed head pattern and one
common native-port extent. Neither contains the accumulated cut prefix. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsBankFields
open LocalBitMultitape CloseoutRowsLoopLayout CloseoutRowsPreparationBounds
open CloseoutRowsPreparationFits CloseoutRowsPreparationInput
open RepairSource.VerifierDecoding RepairRepresentation RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raised (i : Fin 113) : Bool :=
  decide (i=15 ∨ i=18 ∨ i=24 ∨ i=35 ∨ i=37 ∨ i=38 ∨ i=45 ∨ i=46 ∨ i=112)
def heads (out : List Bool) (i : Fin 113) := if i=31 then out.length else if raised i then 1 else 0

theorem native_heads {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) :
    inputHeads gs p F w j rows out = fun i=>heads out (i.castAdd 1) := by
  funext i
  fin_cases i <;> rfl

theorem polynomial_heads {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) :
    (CloseoutRowsPolynomial.input gs p F Q w C rows out).heads=heads out := by
  funext i
  refine Fin.addCases (m:=112) (n:=1) (fun j=>?_) (fun j=>?_) i
  · simpa only [CloseoutRowsPolynomial.input,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
      Fin.addCases_left,CloseoutRowsDegreeLoop.entry] using congrFun (native_heads gs p F w 0 rows out) j
  · fin_cases j
    rfl

theorem cache_bounds {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q : ℕ)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p ≤ F) :
    (exactListWord gs).length+1 ≤ F ∧
      RowCachedCoordinateBounds.inner (RowCachedCoordinateBounds.width gs)+1 ≤ F ∧
      RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs) ≤ F := by
  have hlarge : 16384*RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs) ≤ F := by
    unfold RowCommonBounds.capacity at hF
    have hmono := Nat.mul_le_mul_right (16384*RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs))
      (show 1 ≤ gs.length*Q+1 by omega)
    nlinarith
  refine ⟨?_,?_,(RowCommonBounds.inner_fits gs (gs.length*Q) p).trans hF⟩
  · unfold RowCachedCoordinateBounds.size RowCachedCoordinateBounds.width at hlarge
    omega
  · unfold RowCachedCoordinateBounds.size at hlarge
    unfold RowCachedCoordinateBounds.inner
    omega

theorem common_bound {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w : ℕ) (out : List Bool) (hF : RowCommonBounds.capacity gs (gs.length*Q) p ≤ F)
    (i : Fin 35) (hi : i≠31) :
    (RowCommonReusable.data gs 0 p F [] out [] i).length ≤ capacity n p F w gs.length Q := by
  obtain ⟨hcache,hinner,houter⟩ := cache_bounds gs p F Q hF
  simp only [RowCachedCoordinateBounds.width] at hinner houter
  have hsmall := small_fits n p F w gs.length Q
  unfold scale at hsmall
  fin_cases i <;> first | contradiction |
    simp [RowCommonReusable.data,RowOccurrenceLoop.word,CompareMachine.word,UnaryTemplate.tape,
      RowCachedCoordinateBounds.width]
  all_goals omega

theorem native_bound {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w j : ℕ) (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : rows.length ≤ 2^w) (hj : j ≤ Q)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p ≤ F)
    (i : Fin 49) (hi : i≠31) :
    ((rawInput gs p F w j rows out).tapes (i.castAdd 54)).length ≤ capacity n p F w gs.length Q := by
  let C := capacity n p F w gs.length Q
  have hsmall := small_fits n p F w gs.length Q
  have hcursor := cursor_fits n p F w gs.length Q rows.length (j+1) hM (by omega)
  have hlookup : RowMaskLookupReusable.capacity gs.length w rows.length ≤ C := by
    change RowMaskLookupReusable.capacity gs.length w rows.length ≤ capacity n p F w gs.length Q
    unfold RowTupleCursorReady.capacity RowTupleMaskLoop.budget RowTupleMaskBody.budget at hcursor
    nlinarith
  have hflat : rows.flatten.length=rows.length*gs.length := by
    clear hM hcursor hlookup
    induction rows with
    | nil => simp
    | cons row rows ih =>
      rw [List.flatten_cons,List.length_append,hl row (by simp),ih (fun x hx=>hl x (by simp [hx]))]
      simp [Nat.add_mul,Nat.add_comm]
  have hmflat : rows.flatten.length ≤ C := by
    rw [hflat]
    have hc := cursor_fits n p F w gs.length Q rows.length 1 hM (by omega)
    unfold RowTupleCursorReady.capacity RowTupleMaskLoop.budget RowTupleMaskBody.budget
      RowMaskLookupReusable.capacity RowMaskLookup.budget at hc
    dsimp only [C]
    nlinarith
  unfold scale at hsmall
  simp only [List.length_flatten] at hmflat
  revert hi
  refine Fin.addCases (m:=48) (n:=1) (fun a=>?_) (fun a=>?_) i
  · intro hi
    have ha : (a.castAdd 41 : Fin 89)≠48 := by
      intro he
      have hv:=congrArg (fun k : Fin 89=>k.val) he
      change a.val=48 at hv
      have hb:=a.isLt
      omega
    change ((rawInput gs p F w j rows out).tapes ((a.castAdd 41).castAdd 14)).length ≤ C
    simp only [rawInput,CloseoutRowsComputedCuts.input,Fin.addCases_left]
    rw [Function.update_of_ne ha]
    change ((CloseoutRowsComputedCuts.body (0 : Fin 1) gs p F w j rows out).tapes
      ((a.castAdd 1).castAdd 40)).length ≤ C
    simp only [CloseoutRowsComputedCuts.body,CloseoutRowsEnumeratedCuts.input,
      TapeEmbedding.config,Fin.addCases_left,CloseoutRowsEnumeratedCuts.core]
    rw [ZeroPadding.pad_length]
    apply max_le
    · unfold RowTupleCursorBody.padding
      split_ifs <;> omega
    · revert hi
      refine Fin.addCases (m:=36) (n:=12) (fun b=>?_) (fun b=>?_) a
      · refine Fin.addCases (m:=35) (n:=1) (fun d=>?_) (fun d=>?_) b
        · intro hi
          simpa only [RowTupleCursorLayout.data,Fin.addCases_left] using
            common_bound gs p F Q w out hF d (by intro he; subst d; exact hi rfl)
        · intro _
          fin_cases d
          change (CompareMachine.word (n+1)).length ≤ C
          simp only [CompareMachine.word,List.length_cons,List.length_replicate]
          dsimp only [C]
          omega
      · intro _
        fin_cases b <;> simp [RowTupleCursorLayout.data,Fin.addCases,CompareMachine.word,UnaryTemplate.tape,
          frame_length,SignedSortKey.binary_length]
        all_goals change _ ≤ C
        all_goals dsimp only [C] at *
        all_goals omega
  · intro _
    fin_cases a
    simp [rawInput,CloseoutRowsComputedCuts.input,Fin.addCases]

end NearCubicWires.RepairOrdinary.CloseoutRowsBankFields
