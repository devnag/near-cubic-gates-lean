import Proof.CaseAnalysis.RowsPacketPolynomial

/-! Native packets depend only on their source polynomial and fixed row
metadata. The accumulated cut output is absent from every packet field. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPacketIndependent
open CloseoutRowsPacketPolynomial CloseoutRowsBankPacket CloseoutRowsBankPorts
open LocalBitMultitape CloseoutRowsLoopLayout RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem vector_away {α : Type} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a32 a33 a34 x y : α)
    (i : Fin 35) (hi : i≠31) :
    (![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26,a27,a28,a29,a30,x,a32,a33,a34] : Fin 35→α) i=![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26,a27,a28,a29,a30,y,a32,a33,a34] i := by
  fin_cases i <;> simp_all

private theorem common_out {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F : ℕ) (out : List Bool) (i : Fin 35) (hi : i≠31) :
    RowCommonReusable.data gs 0 p F [] out [] i=RowCommonReusable.data gs 0 p F [] [] [] i := by
  unfold RowCommonReusable.data
  exact vector_away _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i hi

private theorem cursor_out {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w : ℕ) (rows : List (List Bool)) (out : List Bool) (i : Fin 48) (hi : i≠31) :
    RowTupleCursorLayout.data gs 0 p F w rows.length 1 rows [] out 0 [] i=
      RowTupleCursorLayout.data gs 0 p F w rows.length 1 rows [] [] 0 [] i := by
  revert hi
  refine Fin.addCases (m:=36) (n:=12) (fun a=>?_) (fun a=>?_) i
  · refine Fin.addCases (m:=35) (n:=1) (fun b=>?_) (fun b=>?_) a
    · intro hi
      simp only [RowTupleCursorLayout.data,Fin.addCases_left]
      exact common_out gs p F out b (by intro he; subst b; exact hi rfl)
    · intro _
      simp only [RowTupleCursorLayout.data,Fin.addCases_left,Fin.addCases_right]
  · intro _
    simp only [RowTupleCursorLayout.data,Fin.addCases_right]

private theorem raw_out {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w : ℕ) (rows : List (List Bool)) (out : List Bool) (i : Fin 103) (hi : i≠31) :
    (rawInput gs p F w 0 rows out).tapes i=(rawInput gs p F w 0 rows []).tapes i := by
  revert hi
  refine Fin.addCases (m:=89) (n:=14) (fun a=>?_) (fun a=>?_) i
  · simp only [rawInput,CloseoutRowsComputedCuts.input,Fin.addCases_left]
    by_cases ha : a=48
    · subst a
      intro _
      rw [Function.update_self,Function.update_self]
    rw [Function.update_of_ne ha,Function.update_of_ne ha]
    simp only [CloseoutRowsComputedCuts.body,CloseoutRowsEnumeratedCuts.input,TapeEmbedding.config]
    refine Fin.addCases (m:=49) (n:=40) (fun b=>?_) (fun b=>?_) a
    · simp only [Fin.addCases_left,CloseoutRowsEnumeratedCuts.core]
      refine Fin.addCases (m:=48) (n:=1) (fun c=>?_) (fun c=>?_) b
      · intro hi
        simp only [Fin.addCases_left]
        apply congrArg (ZeroPadding.pad _)
        exact cursor_out gs p F w rows out c (by intro he; subst c; exact hi rfl)
      · intro _
        simp only [Fin.addCases_right]
    · intro _
      simp only [Fin.addCases_right]
  · intro _
    simp only [rawInput,CloseoutRowsComputedCuts.input,Fin.addCases_right]

theorem data_out {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) (i : Fin 113) (hi : i≠31) :
    data gs p F Q w C rows out i=data gs p F Q w C rows [] i := by
  revert hi
  refine Fin.addCases (m:=112) (n:=1) (fun a=>?_) (fun a=>?_) i
  · simp only [data,CloseoutRowsPolynomial.input,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
      Fin.addCases_left,CloseoutRowsDegreeLoop.entry]
    refine Fin.addCases (m:=103) (n:=9) (fun b=>?_) (fun b=>?_) a
    · intro hi
      simp only [inputTapes,Fin.addCases_left]
      apply congrArg (ZeroPadding.pad _)
      exact raw_out gs p F w rows out b (by intro he; subst b; exact hi rfl)
    · intro _
      simp only [inputTapes,Fin.addCases_right]
  · intro _
    simp only [data,CloseoutRowsPolynomial.input,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
      Fin.addCases_right]

theorem word_congr (left right : Fin 113→List Bool)
    (h : ∀ i,i≠31 → left i=right i) : word left=word right := by
  unfold word CloseoutRowsPacketLoad.stream
  apply List.flatMap_congr
  intro j hj
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
  simp only [fields,extend,port,Fin.addCases_left]
  exact congrArg frame (h _ (CloseoutRowsBankClear.work_avoids i).1)

theorem word_out {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) :
    word (data gs p F Q w C rows out)=word (data gs p F Q w C rows []) := by
  exact word_congr _ _ (data_out gs p F Q w C rows out)

theorem packet_length (C : ℕ) (native : Fin 113→List Bool)
    (hb : ∀ i,i≠31 → i≠105 → (native i).length≤C) :
    (word native).length≤110*(2*C+1) := by
  have hh : ∀ js : List (Fin 114), (∀ j∈js,(fields native j).length≤C) →
      (CloseoutRowsPacketLoad.stream (fields native) js).length≤js.length*(2*C+1) := by
    intro js
    induction js with
    | nil => simp [CloseoutRowsPacketLoad.stream]
    | cons j js ih =>
      intro hj
      have h0:=hj j (by simp)
      have h1:=ih (fun k hk=>hj k (by simp [hk]))
      simp only [CloseoutRowsPacketLoad.stream,List.flatMap_cons,List.length_append,frame_length,List.length_cons] at *
      nlinarith
  have h:=hh ports (field_bound C native hb)
  simpa only [word,ports,List.length_map,List.length_finRange] using h

end NearCubicWires.RepairOrdinary.CloseoutRowsPacketIndependent
