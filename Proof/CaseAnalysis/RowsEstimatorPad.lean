import Proof.CaseAnalysis.RowsEstimatorLinearBudget

/-! Paid allocation after the mandatory cold prefix. Each existing bit is
read and written unchanged; the same pass supplies all missing zero cells.
The unary D driver is retained and the ordinary rewind produces its log. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Pad
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem write_current (bits : List Bool) (k : ℕ) :
    writeTapeBit bits k (readTapeBit bits k)=ZeroPadding.pad (k+1) bits := by
  induction k generalizing bits with
  | zero => cases bits <;> simp [writeTapeBit,readTapeBit,List.getD,ZeroPadding.pad]
  | succ k ih =>
    cases bits with
    | nil => simpa [writeTapeBit,readTapeBit,List.getD,ZeroPadding.pad_nil_succ] using
        congrArg (List.cons false) (ih [])
    | cons bit bits =>
      simpa [writeTapeBit,readTapeBit,List.getD,ZeroPadding.pad_cons] using
        congrArg (List.cons bit) (ih bits)

theorem pad_successive (bits : List Bool) (k : ℕ) :
    ZeroPadding.pad (k+1) (ZeroPadding.pad k bits)=ZeroPadding.pad (k+1) bits := by
  simp only [ZeroPadding.pad,List.length_append,List.length_replicate,List.append_assoc]
  rw [← List.replicate_add]
  congr 2
  omega

def raw (t : ℕ) : Machine (t+1) 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q bs=>if q.val=0 then
    if bs ((0 : Fin 1).natAdd t) then
      some ⟨0,Fin.addCases (fun i=>some (bs (i.castAdd 1))) (fun _=>none),fun _=>.right⟩
    else some ⟨1,fun _=>none,fun _=>.stay⟩
    else none
def cfg {t : ℕ} (data : Fin t→List Bool) (D k : ℕ) (q : Fin 2) : Configuration (t+1) 2 :=
  ⟨q,fun _=>k,Fin.addCases (fun i=>ZeroPadding.pad k (data i)) (fun _=>List.replicate D true)⟩

theorem next {t : ℕ} (data : Fin t→List Bool) (D k : ℕ) (hk : k<D) :
    step (raw t) (cfg data D k 0)=some (cfg data D (k+1) 0) := by
  have hd : (cfg data D k 0).scanned ((0 : Fin 1).natAdd t)=true := by
    simp [cfg,Configuration.scanned,readTapeBit,List.getD,hk]
  simp only [step,raw,show (cfg data D k 0).control=0 from rfl,Fin.val_zero,ite_true,hd,Option.map_some]
  change some (applyAction (cfg data D k 0)
    ⟨0,Fin.addCases (fun i=>some ((cfg data D k 0).scanned (i.castAdd 1))) (fun _=>none),
      fun _=>.right⟩)=some (cfg data D (k+1) 0)
  congr 1
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction,cfg,HeadMove.apply]
  · funext i
    refine Fin.addCases (m:=t) (n:=1) (fun j=>?_) (fun j=>?_) i
    · simp only [applyAction,cfg,Configuration.scanned,Fin.addCases_left]
      rw [write_current,pad_successive]
    · simp only [applyAction,cfg,Fin.addCases_right]

theorem stop {t : ℕ} (data : Fin t→List Bool) (D : ℕ) :
    step (raw t) (cfg data D D 0)=some (cfg data D D 1) := by
  simp [step,raw,cfg,Configuration.scanned,readTapeBit,List.getD]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction,HeadMove.apply]
  · rfl

theorem raw_run {t : ℕ} (data : Fin t→List Bool) (D : ℕ) : ∃ r,
    runFrom (raw t) (D+1) (cfg data D 0 0)=some r ∧
      r.final=cfg data D D 1 ∧ r.steps=D+1 := by
  have loop (left k : ℕ) (he : k+left=D) : ∃ r,
      runFrom (raw t) (left+1) (cfg data D k 0)=some r ∧
        r.final=cfg data D D 1 ∧ r.steps=left+1 := by
    induction left generalizing k with
    | zero =>
      have hk : k=D := by omega
      subst k
      let done : ExecutionReceipt (t+1) 2 :=
        ⟨cfg data D D 1,0,(cfg data D D 1).tapeCells⟩
      have hr : runFrom (raw t) 0 (cfg data D D 1)=some done := by
        simp [runFrom,raw,cfg,done]
      exact ⟨_,runFrom_step (raw t) _ _ done (by simp [raw,cfg]) (stop data D) hr,rfl,rfl⟩
    | succ left ih =>
      obtain ⟨r,hr,hf,hs⟩:=ih (k+1) (by omega)
      exact ⟨_,runFrom_step (raw t) _ _ r (by simp [raw,cfg]) (next data D k (by omega)) hr,
        hf,by dsimp;omega⟩
  exact loop D 0 (by omega)

def machine (t : ℕ) := Rewind.machine (raw t)
def input {t : ℕ} (data : Fin t→List Bool) (D : ℕ) : Fin (t+1+1)→List Bool :=
  Fin.addCases (Fin.addCases data (fun _ : Fin 1=>List.replicate D true)) (fun _ : Fin 1=>[])
def output {t : ℕ} (data : Fin t→List Bool) (D : ℕ) : Fin (t+1+1)→List Bool :=
  Fin.addCases (Fin.addCases (fun i=>ZeroPadding.pad D (data i)) (fun _ : Fin 1=>List.replicate D true))
    (fun _ : Fin 1=>List.replicate (D+1) false)

theorem ready {t : ℕ} (data : Fin t→List Bool) (D : ℕ) :
    ReadyRun (machine t) (2*D+4) (input data D) (output data D) := by
  obtain ⟨base,hb,bf,bs⟩:=raw_run data D
  obtain ⟨r,hr,rf,rs,_⟩:=Rewind.recorded_run (raw t) (D+1) (cfg data D 0 0) base hb 0 (by intro i;rfl)
  have hi : Rewind.recording (cfg data D 0 0) 0=initialConfiguration (machine t) (input data D) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=t+1) (n:=1) (fun j=>?_) (fun j=>?_) i <;>
        simp [Rewind.recording,Rewind.config,cfg,initialConfiguration]
    · funext i
      refine Fin.addCases (m:=t+1) (n:=1) (fun j=>?_) (fun j=>?_) i
      · refine Fin.addCases (m:=t) (n:=1) (fun a=>?_) (fun a=>?_) j
        · simp [Rewind.recording,Rewind.config,cfg,input,initialConfiguration,ZeroPadding.pad_zero]
        · simp [Rewind.recording,Rewind.config,cfg,input,initialConfiguration]
      · simp [Rewind.recording,Rewind.config,input,initialConfiguration]
  rw [hi,bs,Nat.zero_add] at hr
  have hc : 2*(D+1)+2=2*D+4 := by omega
  rw [hc] at hr
  refine ⟨r,hr,?_,?_,?_⟩
  · rw [rf,bf,bs];simp only [Rewind.finished,Rewind.config,cfg,Nat.zero_add];rfl
  · intro i;rw [rf]
    refine Fin.addCases (m:=t+1) (n:=1) (fun j=>?_) (fun j=>?_) i <;>
      simp [Rewind.finished,Rewind.config]
  · rw [rs,bs];omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Pad
