import Proof.CaseAnalysis.RowsEstimatorMetadataBatch

/-! One ordinary pass distributes retained metadata, including repeated
source fields, and initializes every blank destination at the same capacity. -/
namespace NearCubicWires.ExtIncidence.NativeFanout
open LocalBitMultitape RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairOrdinary.RecoveryExecution RepairOrdinary.RecoveryBoundedTapeCopy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def word {k m : ℕ} (select : Fin m→Option (Fin k)) (data : Fin k→List Bool)
    (i : Fin m) : List Bool:= (select i).elim [] data

def bit {k m : ℕ} (select : Fin m→Option (Fin k)) (bs : Fin (k+(m+1))→Bool)
    (i : Fin m) : Bool:= (select i).elim false (fun j=>bs (j.castAdd (m+1)))

def raw {k m : ℕ} (select : Fin m→Option (Fin k)) : Machine (k+(m+1)) 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q bs => if q.val=0 then
    if bs (((0 : Fin 1).natAdd m).natAdd k) then
      some ⟨0,Fin.addCases (fun _ : Fin k => none)
        (Fin.addCases (fun i : Fin m => some (bit select bs i)) (fun _ : Fin 1 => none)),
        fun _ => .right⟩
    else some ⟨1,fun _ => none,fun _ => .stay⟩
    else none

def cfg {k m : ℕ} (select : Fin m→Option (Fin k)) (data : Fin k → List Bool) (D n : ℕ) (q : Fin 2) : Configuration (k+(m+1)) 2 :=
  ⟨q,fun _ => n,Fin.addCases data
    (Fin.addCases (fun i => copied (word select data i) n) (fun _ : Fin 1 => List.replicate D true))⟩

theorem next {k m : ℕ} (select : Fin m→Option (Fin k)) (data : Fin k → List Bool) (D n : ℕ) (hn : n<D) :
    step (raw select) (cfg select data D n 0)=some (cfg select data D (n+1) 0) := by
  have hd : (cfg select data D n 0).scanned (((0 : Fin 1).natAdd m).natAdd k)=true := by
    simp [cfg,Configuration.scanned,readTapeBit,List.getD,hn]
  simp only [step,raw,show (cfg select data D n 0).control=0 from rfl,Fin.val_zero,ite_true,hd,Option.map_some]
  change some (applyAction (cfg select data D n 0)
    ⟨0,Fin.addCases (fun _ : Fin k => none)
      (Fin.addCases (fun i : Fin m => some (bit select (cfg select data D n 0).scanned i))
        (fun _ : Fin 1 => none)),fun _ => .right⟩)=some (cfg select data D (n+1) 0)
  congr 1
  apply configuration_ext
  · rfl
  · funext i;simp [applyAction,cfg,HeadMove.apply]
  · funext i
    refine Fin.addCases (m:=k) (n:=m+1) (fun j => ?_) (fun j => ?_) i
    · simp only [applyAction,cfg,Fin.addCases_left]
    · refine Fin.addCases (m:=m) (n:=1) (fun j => ?_) (fun j => ?_) j
      · have hb : bit select (cfg select data D n 0).scanned j=readTapeBit (word select data j) n:=by
          cases h : select j <;> simp [bit,word,h,Configuration.scanned,cfg,readTapeBit,List.getD]
        simp only [applyAction,cfg,Fin.addCases_left,Fin.addCases_right,prefix_succ]
        change writeTapeBit (copied (word select data j) n) n
          (bit select (cfg select data D n 0).scanned j)=_
        rw [hb]
        simpa only [prefix_length] using Streaming.write_append
          (copied (word select data j) n) (readTapeBit (word select data j) n)
      · simp only [applyAction,cfg,Fin.addCases_right]

theorem stop {k m : ℕ} (select : Fin m→Option (Fin k)) (data : Fin k → List Bool) (D : ℕ) :
    step (raw select) (cfg select data D D 0)=some (cfg select data D D 1) := by
  simp [step,raw,cfg,Configuration.scanned,readTapeBit,List.getD]
  apply configuration_ext
  · rfl
  · funext i;simp [applyAction,HeadMove.apply]
  · rfl

theorem raw_run {k m : ℕ} (select : Fin m→Option (Fin k)) (data : Fin k → List Bool) (D : ℕ) : ∃ r,
    runFrom (raw select) (D+1) (cfg select data D 0 0)=some r ∧
      r.final=cfg select data D D 1 ∧ r.steps=D+1 := by
  have loop (left n : ℕ) (he : n+left=D) : ∃ r,
      runFrom (raw select) (left+1) (cfg select data D n 0)=some r ∧
        r.final=cfg select data D D 1 ∧ r.steps=left+1 := by
    induction left generalizing n with
    | zero =>
      have hn : n=D := by omega
      subst n
      let done : ExecutionReceipt (k+(m+1)) 2 := ⟨cfg select data D D 1,0,(cfg select data D D 1).tapeCells⟩
      have hr : runFrom (raw select) 0 (cfg select data D D 1)=some done := by simp [runFrom,raw,cfg,done]
      exact ⟨_,runFrom_step (raw select) _ _ done (by simp [raw,cfg]) (stop select data D) hr,rfl,rfl⟩
    | succ left ih =>
      obtain ⟨r,hr,hf,hs⟩ := ih (n+1) (by omega)
      exact ⟨_,runFrom_step (raw select) _ _ r (by simp [raw,cfg]) (next select data D n (by omega)) hr,
        hf,by dsimp;omega⟩
  exact loop D 0 (by omega)

def machine {k m : ℕ} (select : Fin m→Option (Fin k)):=Rewind.machine (raw select)
def input {k m : ℕ} (data : Fin k→List Bool) (D : ℕ) : Fin (k+(m+1)+1)→List Bool:=
  Fin.addCases (Fin.addCases data (Fin.addCases (fun _ : Fin m=>[]) (fun _ : Fin 1=>List.replicate D true)))
    (fun _ : Fin 1=>[])
def output {k m : ℕ} (select : Fin m→Option (Fin k)) (data : Fin k→List Bool)
    (D : ℕ) : Fin (k+(m+1)+1)→List Bool:=
  Fin.addCases (Fin.addCases data (Fin.addCases (fun i=>ZeroPadding.pad D (word select data i))
    (fun _ : Fin 1=>List.replicate D true))) (fun _ : Fin 1=>List.replicate (D+1) false)

theorem ready {k m : ℕ} (select : Fin m→Option (Fin k)) (data : Fin k→List Bool)
    (D : ℕ) (hD : ∀ i,(data i).length ≤ D) :
    ReadyRun (machine select) (2*D+4) (input data D) (output select data D):=by
  obtain ⟨base,hb,bf,bs⟩:=raw_run select data D
  have hi : cfg select data D 0 0=initialConfiguration (raw select)
      (Fin.addCases data (Fin.addCases (fun _ : Fin m=>[]) (fun _ : Fin 1=>List.replicate D true))):=rfl
  rw [hi] at hb
  obtain ⟨r,hr,ht,hlog,hh,hs,_⟩:=Rewind.Workspace.reset_workspace (raw select) _ _ base hb 0
  have time : 2*base.steps+2=2*D+4:=by omega
  rw [time] at hr
  refine ⟨r,hr,?_,hh,hs.trans time⟩
  funext i
  refine Fin.addCases (m:=k+(m+1)) (n:=1) (fun j=>?_) (fun j=>?_) i
  · rw [ht,bf]
    refine Fin.addCases (m:=k) (n:=m+1) (fun a=>?_) (fun a=>?_) j
    · simp only [cfg,output,Fin.addCases_left]
    · refine Fin.addCases (m:=m) (n:=1) (fun a=>?_) (fun a=>?_) a
      · simp only [cfg,output,Fin.addCases_left,Fin.addCases_right]
        apply CloseoutRowsMetadataCopy.copied_pad
        cases h : select a with
        | none => simp [word,h]
        | some j => simpa only [word,h,Option.elim_some] using hD j
      · simp only [cfg,output,Fin.addCases_left,Fin.addCases_right]
  · have hj : j=0:=Fin.eq_zero j
    subst j
    simp only [output,Fin.addCases_right]
    simpa only [Nat.zero_max,bs] using hlog

end NearCubicWires.ExtIncidence.NativeFanout
