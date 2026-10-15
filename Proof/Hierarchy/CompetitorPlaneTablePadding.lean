import Proof.Hierarchy.CompetitorPlaneTableInitialize

/-! The table dimension dock physically extends all selected fields to its
generated D-cell capacity in one sweep. Existing bits are retained; blank
accumulator/work fields become actual zero buffers. The sweep and rewind
cost 2D+4, independent of the number of cells in the packet source. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlaneTablePadding
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem write_self_pad (tape : List Bool) (pos : ℕ) :
    writeTapeBit (ZeroPadding.pad pos tape) pos (readTapeBit tape pos)=ZeroPadding.pad (pos+1) tape := by
  induction pos generalizing tape with
  | zero => cases tape <;> simp [ZeroPadding.pad,writeTapeBit,readTapeBit,List.getD]
  | succ pos ih =>
    cases tape with
    | nil =>
      simpa [ZeroPadding.pad_nil_succ,writeTapeBit,readTapeBit,List.getD] using congrArg (List.cons false) (ih [])
    | cons b tape =>
      simpa [ZeroPadding.pad_cons,writeTapeBit,readTapeBit,List.getD] using congrArg (List.cons b) (ih tape)

def raw (t : ℕ) : Machine (t+1) 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q bits => if q.val=0 then
    if bits ((0 : Fin 1).natAdd t) then some ⟨0,
      Fin.addCases (m := t) (n := 1) (motive := fun _ => Option Bool)
        (fun i => some (bits (i.castAdd 1))) (fun _ => none),fun _ => .right⟩
    else some ⟨1,fun _ => none,fun _ => .stay⟩
  else none
def tapes {t : ℕ} (total pos : ℕ) (fields : Fin t → List Bool) : Fin (t+1) → List Bool :=
  Fin.addCases (m := t) (n := 1) (motive := fun _ => List Bool)
    (fun i => ZeroPadding.pad pos (fields i)) (fun _ => List.replicate total true)
def cfg {t : ℕ} (q : Fin 2) (total pos : ℕ) (fields : Fin t → List Bool) : Configuration (t+1) 2 :=
  ⟨q,fun _ => pos,tapes total pos fields⟩

theorem sweep_step {t : ℕ} (total pos : ℕ) (fields : Fin t → List Bool) (hp : pos<total) :
    step (raw t) (cfg 0 total pos fields)=some (cfg 0 total (pos+1) fields) := by
  have hread : readTapeBit (List.replicate total true) pos=true := by simp [readTapeBit,hp]
  simp only [step,raw,cfg,Configuration.scanned,tapes,Fin.addCases_right,hread,Fin.val_zero,↓reduceIte]
  apply congrArg some
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (m := t) (n := 1) ?_ ?_ i
    · intro j
      simp only [applyAction,Fin.addCases_left,ZeroPadding.read_pad]
      exact write_self_pad _ _
    · intro j
      simp only [applyAction,Fin.addCases_right]

theorem stop_step {t : ℕ} (total : ℕ) (fields : Fin t → List Bool) :
    step (raw t) (cfg 0 total total fields)=some (cfg 1 total total fields) := by
  have hread : readTapeBit (List.replicate total true) total=false := by simp [readTapeBit]
  simp only [step,raw,cfg,Configuration.scanned,tapes,Fin.addCases_right,hread,Fin.val_zero,↓reduceIte]
  rfl

theorem sweep {t : ℕ} (remaining pos : ℕ) (fields : Fin t → List Bool) :
    Timed (raw t) (remaining+1) (cfg 0 (pos+remaining) pos fields)
      (cfg 1 (pos+remaining) (pos+remaining) fields) := by
  induction remaining generalizing pos with
  | zero => simpa using Timed.single (by rfl) (stop_step pos fields)
  | succ remaining ih =>
    have ht := ih (pos+1)
    have he : pos+1+remaining=pos+(remaining+1) := by omega
    rw [he] at ht
    exact Timed.step (by rfl) (sweep_step _ _ fields (by omega)) ht

def machine (t : ℕ) := Rewind.machine (raw t)
def input {t : ℕ} (D : ℕ) (fields : Fin t → List Bool) : Fin (t+1+1) → List Bool :=
  Fin.addCases (m := t+1) (n := 1) (motive := fun _ => List Bool)
    (Fin.addCases (m := t) (n := 1) (motive := fun _ => List Bool) fields (fun _ => List.replicate D true)) (fun _ => [])
def output {t : ℕ} (D : ℕ) (fields : Fin t → List Bool) : Fin (t+1+1) → List Bool :=
  Fin.addCases (m := t+1) (n := 1) (motive := fun _ => List Bool)
    (tapes D D fields) (fun _ => List.replicate (D+1) false)

theorem padding_ready {t : ℕ} (D : ℕ) (fields : Fin t → List Bool) :
    ReadyRun (machine t) (2*D+4) (input D fields) (output D fields) := by
  obtain ⟨base,hr,hf,hs⟩ := (sweep D 0 fields).run (by rfl)
  have hi : cfg 0 (0+D) 0 fields=initialConfiguration (raw t)
      (Fin.addCases (m := t) (n := 1) (motive := fun _ => List Bool) fields (fun _ => List.replicate D true)) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      refine Fin.addCases (m := t) (n := 1) ?_ ?_ i <;> intro j <;> simp [cfg,tapes,initialConfiguration]
  rw [hi] at hr
  obtain ⟨r,hrun,ht,hc,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace (raw t) _ _ base hr 0
  have he : 2*base.steps+2=2*D+4 := by omega
  rw [he] at hrun
  refine ⟨r,hrun,?_,hh,hsteps.trans he⟩
  funext i
  refine Fin.addCases (m := t+1) (n := 1) ?_ ?_ i
  · intro j
    simpa only [hf,cfg,Nat.zero_add,output,Fin.addCases_left] using ht j
  · intro j
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    simp only [output,Fin.addCases_right]
    simpa only [hs,Nat.zero_add,Nat.zero_max] using hc

end NearCubicWires.RepairOrdinary.CompetitorPlaneTablePadding
