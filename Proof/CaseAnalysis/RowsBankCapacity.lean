import Proof.CaseAnalysis.RowsBankFields

/-! One common C bounds every native port at both ends of a polynomial.
The global append output is excluded, and the erase log has exactly C+1 cells. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsBankCapacity
open LocalBitMultitape CloseoutRowsLoopLayout CloseoutRowsPreparationBounds
open CloseoutRowsPreparationFits CloseoutRowsPreparationInput CloseoutRowsBankFields
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacities (C : ℕ) (i : Fin 113) := if i=31 then 0 else if i=105 then C+1 else C

theorem enum_bound {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w j : ℕ) (rows : List (List Bool)) (out : List Bool) (hj : j ≤ Q) (i : Fin 40) :
    ((rawInput gs p F w j rows out).tapes ((i.natAdd 49).castAdd 14)).length ≤ capacity n p F w gs.length Q := by
  have hm := small_fits n p F w gs.length Q
  unfold scale at hm
  have hi : (i.natAdd 49 : Fin 89)≠48 := by
    intro h
    have hv:=congrArg Fin.val h
    change 49+i.val=48 at hv
    omega
  simp only [rawInput,CloseoutRowsComputedCuts.input,Fin.addCases_left,Function.update_of_ne hi,
    CloseoutRowsComputedCuts.body,CloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,Fin.addCases_right]
  simp only [RowTupleEnumeratedEquations.extra]
  split_ifs <;> simp [CompareMachine.word,frame_length,SignedSortKey.binary_length] <;> omega

theorem coefficient_bound {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w j : ℕ) (rows : List (List Bool)) (out : List Bool) (hj : j ≤ Q) (i : Fin 14) :
    ((rawInput gs p F w j rows out).tapes (i.natAdd 89)).length ≤ capacity n p F w gs.length Q := by
  have hm := small_fits n p F w gs.length Q
  unfold scale at hm
  simp only [rawInput,CloseoutRowsComputedCuts.input,Fin.addCases_right]
  fin_cases i <;> simp [CloseoutRowsDegreeCoefficient.input] <;> omega

theorem raw_bound {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w j : ℕ) (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : rows.length ≤ 2^w) (hj : j ≤ Q)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p ≤ F)
    (i : Fin 103) (hi : i≠31) :
    ((rawInput gs p F w j rows out).tapes i).length ≤ capacity n p F w gs.length Q := by
  revert hi
  refine Fin.addCases (m:=89) (n:=14) (fun a=>?_) (fun a=>?_) i
  · refine Fin.addCases (m:=49) (n:=40) (fun b=>?_) (fun b=>?_) a
    · intro hi
      exact native_bound gs p F Q w j rows out hl hM hj hF b (by intro he; subst b; exact hi rfl)
    · intro _
      exact enum_bound gs p F Q w j rows out hj b
  · intro _
    exact coefficient_bound gs p F Q w j rows out hj a

theorem input_bound {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w j : ℕ) (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : rows.length ≤ 2^w) (hj : j ≤ Q)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p ≤ F)
    (i : Fin 112) (hi : i≠31) (hlog : i≠105) :
    (inputTapes gs p F w j (capacity n p F w gs.length Q) rows out i).length ≤ capacity n p F w gs.length Q := by
  have hm := small_fits n p F w gs.length Q
  unfold scale at hm
  revert hi hlog
  refine Fin.addCases (m:=103) (n:=9) (fun a=>?_) (fun a=>?_) i
  · intro hi _
    simp only [inputTapes,Fin.addCases_left,ZeroPadding.pad_length]
    apply max_le
    · unfold CloseoutRowsDegreeReset.caps
      split_ifs <;> omega
    · exact raw_bound gs p F Q w j rows out hl hM hj hF a (by intro he; subst a; exact hi rfl)
  · intro _ hlog
    fin_cases a <;> first | (exact False.elim (hlog rfl)) |
      simp [inputTapes,extra,templates,Fin.addCases,CompareMachine.word,frame_length,SignedSortKey.binary_length]
    all_goals omega

theorem loop_heads {s n : ℕ} (body : Machine 112 s) (gs : List (ExactThresholdGate n))
    (phase : Fin 5) (p F Q w j C : ℕ) (rows : List (List Bool)) (out : List Bool) :
    (RepeatMachine.cfg phase (CloseoutRowsDegreeLoop.entry body gs p F w j C rows out) Q 1).heads=heads out := by
  funext i
  refine Fin.addCases (m:=112) (n:=1) (fun a=>?_) (fun a=>?_) i
  · simpa only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left,CloseoutRowsDegreeLoop.entry]
      using congrFun (native_heads gs p F w j rows out) a
  · fin_cases a
    rfl

theorem loop_bound {s n : ℕ} (body : Machine 112 s) (gs : List (ExactThresholdGate n))
    (phase : Fin 5) (p F Q w j : ℕ) (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : rows.length ≤ 2^w) (hj : j ≤ Q)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p ≤ F)
    (i : Fin 113) (hi : i≠31) (hlog : i≠105) :
    ((RepeatMachine.cfg phase (CloseoutRowsDegreeLoop.entry body gs p F w j
      (capacity n p F w gs.length Q) rows out) Q 1).tapes i).length ≤ capacity n p F w gs.length Q := by
  revert hi hlog
  refine Fin.addCases (m:=112) (n:=1) (fun a=>?_) (fun a=>?_) i
  · intro hi hlog
    simpa only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left,CloseoutRowsDegreeLoop.entry]
      using input_bound gs p F Q w j rows out hl hM hj hF a
        (by intro he; subst a; exact hi rfl) (by intro he; subst a; exact hlog rfl)
  · intro _ _
    fin_cases a
    change (CompareMachine.word Q).length ≤ capacity n p F w gs.length Q
    have hm := small_fits n p F w gs.length Q
    unfold scale at hm
    simp only [CompareMachine.word,List.length_cons,List.length_replicate]
    omega

theorem loop_driver {s n : ℕ} (body : Machine 112 s) (gs : List (ExactThresholdGate n))
    (phase : Fin 5) (p F Q w j C : ℕ) (rows : List (List Bool)) (out : List Bool) :
    (RepeatMachine.cfg phase (CloseoutRowsDegreeLoop.entry body gs p F w j C rows out) Q 1).tapes 104=
      List.replicate C true ∧
    (RepeatMachine.cfg phase (CloseoutRowsDegreeLoop.entry body gs p F w j C rows out) Q 1).tapes 105=
      List.replicate (C+1) false := by constructor <;> rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsBankCapacity
