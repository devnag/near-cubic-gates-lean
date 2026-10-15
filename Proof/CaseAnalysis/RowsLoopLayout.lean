import Proof.CaseAnalysis.RowsReusableCuts
import Proof.CaseAnalysis.RowsMetadataReload
import Proof.CaseAnalysis.RowsDegreeNext

/-! One exact boundary for the degree loop: native row context, 57 work
tapes, the retained C driver/logs, and six short templates. The worker
receipt describes every physical head and tape needed by its next call. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsLoopLayout
open LocalBitMultitape RecoveryExecution CloseoutRowsDegreeReset
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def templates (p w M j : ℕ) : Fin 6→List Bool :=
  ![CompareMachine.word w,frame (SignedSortKey.binary w (M-1)),CompareMachine.word (j+1),
    List.replicate w true,List.replicate j true,List.replicate p true]
def extra (p w M j C : ℕ) : Fin 9→List Bool :=
  Fin.addCases (m:=3) (n:=6) (motive:=fun _=>List Bool)
    ![List.replicate C false,List.replicate C true,List.replicate (C+1) false] (templates p w M j)
noncomputable def rawInput {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  CloseoutRowsComputedCuts.input (0 : Fin 1) gs p F w j rows out
noncomputable def inputHeads {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) : Fin 112→ℕ :=
  Fin.addCases (m:=103) (n:=9) (motive:=fun _=>ℕ) (rawInput gs p F w j rows out).heads (fun _=>0)
noncomputable def inputTapes {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) : Fin 112→List Bool :=
  Fin.addCases (m:=103) (n:=9) (motive:=fun _=>List Bool)
    (fun i=>ZeroPadding.pad (caps C i) ((rawInput gs p F w j rows out).tapes i))
    (extra p w rows.length j C)
noncomputable def nativeEnd {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  CloseoutRowsEnumeratedCuts.finished (0 : Fin 1) gs p F w (j+1) rows out ((-2 : ℤ)^j)
noncomputable def finalHeads {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) : Fin 112→ℕ :=
  Fin.addCases (m:=49) (n:=63) (motive:=fun _=>ℕ)
    (fun i=>if selected (i.castAdd 54) then 0 else (nativeEnd gs p F w j rows out).heads i) (fun _=>0)
noncomputable def finalTapes {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) : Fin 112→List Bool :=
  Fin.addCases (m:=103) (n:=9) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=49) (n:=54) (motive:=fun _=>List Bool)
      (fun i=>if selected (i.castAdd 54) then List.replicate C false else
        (nativeEnd gs p F w j rows out).tapes i) (fun _=>List.replicate C false))
    (extra p w rows.length j C)
noncomputable def worker := TapeEmbedding.machine 6 CloseoutRowsReusableCuts.machine

theorem old_selected (i : Fin 54) : selected (i.natAdd 49)=true := by
  apply decide_eq_true
  right; right; right
  dsimp
  omega

theorem worker_run {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w j C : ℕ) (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length)
    (hw : rows.length<2^w) (hj : j<Q) (hQp : Q≤p)
    (hp : RowTupleFixedCapacity.width gs Q≤p)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F)
    (hc : CloseoutRowsComputedCuts.budget gs p F w j rows+1≤C)
    (ht : ∀ i,selected i=true → ((rawInput gs p F w j rows out).tapes i).length≤C) :
    ∃ actual,runFrom worker (CloseoutRowsReusableCuts.budget gs p F w j C rows)
      ⟨worker.start,inputHeads gs p F w j rows out,inputTapes gs p F w j C rows out⟩=some actual ∧
      actual.final.heads=finalHeads gs p F w j rows out ∧
      actual.final.tapes=finalTapes gs p F w j C rows out ∧
      actual.steps≤CloseoutRowsReusableCuts.budget gs p F w j C rows := by
  obtain ⟨raw,hr,rh,rt,_⟩ := CloseoutRowsComputedCuts.cuts_run gs p F Q w j rows out hl hM hw hj hQp hp hF
  obtain ⟨clean,hclean,ch,ct,lh,lt,dh,dt,eh,et,_⟩ := CloseoutRowsDegreeClean.clean_run
    CloseoutRowsComputedCuts.machine _ _ C raw hr
    (CloseoutRowsDegreeReset.input_heads _ gs p F w j rows out) ht hc
  let actual := TapeEmbedding.receipt (fun _ : Fin 6=>0) (templates p w rows.length j) clean
  have he := TapeEmbedding.run_embed CloseoutRowsReusableCuts.machine (fun _ : Fin 6=>0)
    (templates p w rows.length j) _ _ clean hclean
  have hi : TapeEmbedding.config (fun _ : Fin 6=>0) (templates p w rows.length j)
      (CloseoutRowsReusableCuts.input gs p F w j C rows out)=
      (⟨worker.start,inputHeads gs p F w j rows out,inputTapes gs p F w j C rows out⟩ :
        Configuration 112 _) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=103) (n:=9) (fun k=>?_) (fun k=>?_) i
      · change (TapeEmbedding.config (fun _ : Fin 6=>0) (templates p w rows.length j)
          (CloseoutRowsReusableCuts.input gs p F w j C rows out)).heads
          (((k.castAdd 1).castAdd 2).castAdd 6)=_
        simp only [TapeEmbedding.config,Fin.addCases_left,CloseoutRowsReusableCuts.input,
          CloseoutRowsDegreeClean.input,Composition.leftConfig,CloseoutRowsDegreeReset.input,
          ZeroPadding.config,Rewind.recording,Rewind.config,inputHeads]
        rfl
      · fin_cases k <;> rfl
    · funext i
      refine Fin.addCases (m:=103) (n:=9) (fun k=>?_) (fun k=>?_) i
      · change (TapeEmbedding.config (fun _ : Fin 6=>0) (templates p w rows.length j)
          (CloseoutRowsReusableCuts.input gs p F w j C rows out)).tapes
          (((k.castAdd 1).castAdd 2).castAdd 6)=_
        simp only [TapeEmbedding.config,Fin.addCases_left,CloseoutRowsReusableCuts.input,
          CloseoutRowsDegreeClean.input,Composition.leftConfig,CloseoutRowsDegreeReset.input,
          ZeroPadding.config,Rewind.recording,Rewind.config,Rewind.Workspace.capacities,
          ZeroPadding.pad_zero,inputTapes]
        rfl
      · fin_cases k <;> rfl
  change runFrom worker (CloseoutRowsReusableCuts.budget gs p F w j C rows)
    (TapeEmbedding.config (fun _ : Fin 6=>0) (templates p w rows.length j)
      (CloseoutRowsReusableCuts.input gs p F w j C rows out))=some actual at he
  rw [hi] at he
  refine ⟨actual,he,?_,?_,runFrom_steps_le worker _ _ _ he⟩
  · funext i
    refine Fin.addCases (m:=103) (n:=9) (fun k=>?_) (fun k=>?_) i
    · change actual.final.heads ((k.castAdd 3).castAdd 6)=_
      rw [TapeEmbedding.receipt_heads_old,ch]
      refine Fin.addCases (m:=49) (n:=54) (fun a=>?_) (fun a=>?_) k
      · have hh := rh a
        change raw.final.heads (a.castAdd 54)=(nativeEnd gs p F w j rows out).heads a at hh
        rw [hh]
        change _=finalHeads gs p F w j rows out (a.castAdd 63)
        simp only [finalHeads,Fin.addCases_left]
      · rw [old_selected]
        simp only [↓reduceIte]
        change 0=finalHeads gs p F w j rows out ((a.castAdd 9).natAdd 49)
        simp only [finalHeads,Fin.addCases_right]
    · fin_cases k
      · exact lh
      · exact dh
      · exact eh
      all_goals rfl
  · funext i
    refine Fin.addCases (m:=103) (n:=9) (fun k=>?_) (fun k=>?_) i
    · change actual.final.tapes ((k.castAdd 3).castAdd 6)=_
      rw [TapeEmbedding.receipt_tapes_old,ct]
      refine Fin.addCases (m:=49) (n:=54) (fun a=>?_) (fun a=>?_) k
      · have htape := rt a
        change raw.final.tapes (a.castAdd 54)=(nativeEnd gs p F w j rows out).tapes a at htape
        rw [htape]
        simp only [finalTapes,Fin.addCases_left]
      · rw [old_selected]
        simp only [↓reduceIte]
        simp only [finalTapes,Fin.addCases_left,Fin.addCases_right]
    · fin_cases k
      · exact lt
      · exact dt
      · exact et
      all_goals rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsLoopLayout
