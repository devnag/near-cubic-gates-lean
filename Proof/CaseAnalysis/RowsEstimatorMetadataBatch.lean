import Proof.CaseAnalysis.RowsEstimatorPad
import Proof.CaseAnalysis.RowsMetadataCopy

/-! All caller metadata fields are copied in parallel in one paid D pass.
The source bank, raw D, and the reusable rewind log are preserved. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.MetadataBatch
open LocalBitMultitape RecoveryRootRound RecoveryExecution RecoveryBoundedTapeCopy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw (k : ℕ) : Machine (k+(k+1)) 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q bs => if q.val=0 then
    if bs (((0 : Fin 1).natAdd k).natAdd k) then
      some ⟨0,Fin.addCases (fun _ : Fin k => none)
        (Fin.addCases (fun i : Fin k => some (bs (i.castAdd (k+1)))) (fun _ : Fin 1 => none)),
        fun _ => .right⟩
    else some ⟨1,fun _ => none,fun _ => .stay⟩
    else none

def cfg {k : ℕ} (data : Fin k → List Bool) (D n : ℕ) (q : Fin 2) : Configuration (k+(k+1)) 2 :=
  ⟨q,fun _ => n,Fin.addCases data
    (Fin.addCases (fun i => copied (data i) n) (fun _ : Fin 1 => List.replicate D true))⟩

theorem next {k : ℕ} (data : Fin k → List Bool) (D n : ℕ) (hn : n<D) :
    step (raw k) (cfg data D n 0)=some (cfg data D (n+1) 0) := by
  have hd : (cfg data D n 0).scanned (((0 : Fin 1).natAdd k).natAdd k)=true := by
    simp [cfg,Configuration.scanned,readTapeBit,List.getD,hn]
  simp only [step,raw,show (cfg data D n 0).control=0 from rfl,Fin.val_zero,ite_true,hd,Option.map_some]
  change some (applyAction (cfg data D n 0)
    ⟨0,Fin.addCases (fun _ : Fin k => none)
      (Fin.addCases (fun i : Fin k => some ((cfg data D n 0).scanned (i.castAdd (k+1))))
        (fun _ : Fin 1 => none)),fun _ => .right⟩)=some (cfg data D (n+1) 0)
  congr 1
  apply configuration_ext
  · rfl
  · funext i;simp [applyAction,cfg,HeadMove.apply]
  · funext i
    refine Fin.addCases (m:=k) (n:=k+1) (fun j => ?_) (fun j => ?_) i
    · simp only [applyAction,cfg,Fin.addCases_left]
    · refine Fin.addCases (m:=k) (n:=1) (fun j => ?_) (fun j => ?_) j
      · simp only [applyAction,cfg,Configuration.scanned,Fin.addCases_left,Fin.addCases_right,prefix_succ]
        simpa only [prefix_length] using Streaming.write_append (copied (data j) n) (readTapeBit (data j) n)
      · simp only [applyAction,cfg,Fin.addCases_right]

theorem stop {k : ℕ} (data : Fin k → List Bool) (D : ℕ) :
    step (raw k) (cfg data D D 0)=some (cfg data D D 1) := by
  simp [step,raw,cfg,Configuration.scanned,readTapeBit,List.getD]
  apply configuration_ext
  · rfl
  · funext i;simp [applyAction,HeadMove.apply]
  · rfl

theorem raw_run {k : ℕ} (data : Fin k → List Bool) (D : ℕ) : ∃ r,
    runFrom (raw k) (D+1) (cfg data D 0 0)=some r ∧
      r.final=cfg data D D 1 ∧ r.steps=D+1 := by
  have loop (left n : ℕ) (he : n+left=D) : ∃ r,
      runFrom (raw k) (left+1) (cfg data D n 0)=some r ∧
        r.final=cfg data D D 1 ∧ r.steps=left+1 := by
    induction left generalizing n with
    | zero =>
      have hn : n=D := by omega
      subst n
      let done : ExecutionReceipt (k+(k+1)) 2 := ⟨cfg data D D 1,0,(cfg data D D 1).tapeCells⟩
      have hr : runFrom (raw k) 0 (cfg data D D 1)=some done := by simp [runFrom,raw,cfg,done]
      exact ⟨_,runFrom_step (raw k) _ _ done (by simp [raw,cfg]) (stop data D) hr,rfl,rfl⟩
    | succ left ih =>
      obtain ⟨r,hr,hf,hs⟩ := ih (n+1) (by omega)
      exact ⟨_,runFrom_step (raw k) _ _ r (by simp [raw,cfg]) (next data D n (by omega)) hr,
        hf,by dsimp;omega⟩
  exact loop D 0 (by omega)

def machine (k : ℕ) := Rewind.machine (raw k)
def input {k : ℕ} (data : Fin k → List Bool) (D : ℕ) : Fin (k+(k+1)+1) → List Bool :=
  Fin.addCases (Fin.addCases data (Fin.addCases (fun _ : Fin k => List.replicate D false)
    (fun _ : Fin 1 => List.replicate D true))) (fun _ : Fin 1 => List.replicate (D+1) false)
def output {k : ℕ} (data : Fin k → List Bool) (D : ℕ) : Fin (k+(k+1)+1) → List Bool :=
  Fin.addCases (Fin.addCases data (Fin.addCases (fun i => ZeroPadding.pad D (data i))
    (fun _ : Fin 1 => List.replicate D true))) (fun _ : Fin 1 => List.replicate (D+1) false)

theorem ready {k : ℕ} (data : Fin k → List Bool) (D : ℕ) (hD : ∀ i,(data i).length ≤ D) :
    ReadyRun (machine k) (2*D+4) (input data D) (output data D) := by
  obtain ⟨base,hb,bf,bs⟩ := raw_run data D
  have hi : cfg data D 0 0=initialConfiguration (raw k)
      (Fin.addCases data (Fin.addCases (fun _ : Fin k => []) (fun _ : Fin 1 => List.replicate D true))) := rfl
  rw [hi] at hb
  obtain ⟨r,hr,ht,hlog,hh,hs,_⟩ := Rewind.Workspace.reset_workspace (raw k) _ _ base hb (D+1)
  have htime : 2*base.steps+2=2*D+4 := by omega
  rw [htime] at hr
  let caps : Fin (k+(k+1)+1) → ℕ :=
    Fin.addCases (Fin.addCases (fun _ : Fin k => 0)
      (Fin.addCases (fun _ : Fin k => D) (fun _ : Fin 1 => 0))) (fun _ : Fin 1 => 0)
  obtain ⟨actual,ha,af,asteps,_⟩ := ZeroPadding.run_config (machine k) caps _ _ r hr
  have hin : ZeroPadding.config caps
      (initialConfiguration (Rewind.machine (raw k)) (Fin.addCases
        (Fin.addCases data (Fin.addCases (fun _ : Fin k => []) (fun _ : Fin 1 => List.replicate D true)))
        (fun _ : Fin 1 => List.replicate (D+1) false)))=
      initialConfiguration (machine k) (input data D) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      refine Fin.addCases (m:=k+(k+1)) (n:=1) (fun j => ?_) (fun j => ?_) i
      · refine Fin.addCases (m:=k) (n:=k+1) (fun j => ?_) (fun j => ?_) j
        · simp [ZeroPadding.config,caps,input,initialConfiguration]
        · refine Fin.addCases (m:=k) (n:=1) (fun j => ?_) (fun j => ?_) j <;>
            simp [ZeroPadding.config,caps,input,initialConfiguration,ZeroPadding.pad]
      · simp [ZeroPadding.config,caps,input,initialConfiguration]
  rw [hin] at ha
  refine ⟨actual,ha,?_,?_,asteps.trans (hs.trans htime)⟩
  · rw [af]
    funext i
    refine Fin.addCases (m:=k+(k+1)) (n:=1) (fun j => ?_) (fun j => ?_) i
    · refine Fin.addCases (m:=k) (n:=k+1) (fun j => ?_) (fun j => ?_) j
      · have hj := ht (j.castAdd (k+1))
        simpa [ZeroPadding.config,caps,output,cfg,bf] using hj
      · refine Fin.addCases (m:=k) (n:=1) (fun j => ?_) (fun j => ?_) j
        · simp only [ZeroPadding.config,caps,output,Fin.addCases_left,Fin.addCases_right]
          have htj := ht ((j.castAdd 1).natAdd k)
          rw [bf] at htj
          simp only [cfg,Fin.addCases_left,Fin.addCases_right] at htj
          rw [htj,CloseoutRowsMetadataCopy.copied_pad (data j) D (hD j)]
          simp [ZeroPadding.pad,hD j]
        · have hj := ht ((j.natAdd k).natAdd k)
          simpa [ZeroPadding.config,caps,output,cfg,bf] using hj
    · fin_cases j
      simpa [ZeroPadding.config,caps,output,bs] using hlog
  · intro i
    rw [af]
    exact hh i

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.MetadataBatch
