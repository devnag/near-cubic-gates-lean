import Proof.Circuits.CanonicalBinaryOutput

/-! Actual midpoint division for the balanced serializer. Alternating writes
split a physical unary count into ceiling/floor halves; a paid rewind restores
all heads. The numeric halves below describe outputs, not supplied fields. -/
namespace NearCubicWires.RepairOrdinary.PCPUnarySplit
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (left : Bool) : Action 3 3 :=
  ⟨if left then 1 else 0,
    ![none,if left then some true else none,if left then none else some true],
    ![.right,if left then .right else .stay,if left then .stay else .right]⟩
def raw : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q bits => if q.val<2 then
    if bits 0 then some (action (q.val==0))
    else some ⟨2,fun _ => none,fun _ => .stay⟩ else none
def cfg (q : Fin 3) (total done left right : ℕ) : Configuration 3 3 :=
  ⟨q,![done,left,right],![List.replicate total true,List.replicate left true,List.replicate right true]⟩

theorem left_step (total done left right : ℕ) (hd : done<total) :
    step raw (cfg 0 total done left right)=some (cfg 1 total (done+1) (left+1) right) := by
  have hb : readTapeBit (List.replicate total true) done=true := by simp [readTapeBit,List.getD,hd]
  simp only [step,raw,cfg,Configuration.scanned,Matrix.cons_val_zero,Fin.val_zero,
    show 0<2 by decide,↓reduceIte,hb,beq_self_eq_true]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i
    · rfl
    · change writeTapeBit (List.replicate left true) left true=List.replicate (left+1) true
      have h := Streaming.write_append (List.replicate left true) true
      simpa only [List.length_replicate,List.replicate_add,List.replicate_one] using h
    · rfl

theorem right_step (total done left right : ℕ) (hd : done<total) :
    step raw (cfg 1 total done left right)=some (cfg 0 total (done+1) left (right+1)) := by
  have hb : readTapeBit (List.replicate total true) done=true := by simp [readTapeBit,List.getD,hd]
  simp only [step,raw,cfg,Configuration.scanned,Matrix.cons_val_zero,
    show (1 : Fin 3).val=1 by rfl,show 1<2 by decide,↓reduceIte,hb]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i
    · rfl
    · rfl
    · change writeTapeBit (List.replicate right true) right true=List.replicate (right+1) true
      have h := Streaming.write_append (List.replicate right true) true
      simpa only [List.length_replicate,List.replicate_add,List.replicate_one] using h

theorem finish_step (q : Fin 3) (hq : q.val<2) (total left right : ℕ) :
    step raw (cfg q total total left right)=some (cfg 2 total total left right) := by
  have hb : readTapeBit (List.replicate total true) total=false := by simp [readTapeBit,List.getD]
  simp only [step,raw,cfg,Configuration.scanned,Matrix.cons_val_zero,hq,↓reduceIte,hb]
  rfl

theorem cycles (pairs total done left right : ℕ) (hfit : done+2*pairs ≤ total) :
    Timed raw (2*pairs) (cfg 0 total done left right)
      (cfg 0 total (done+2*pairs) (left+pairs) (right+pairs)) := by
  induction pairs generalizing done left right with
  | zero => simpa using Timed.refl raw (cfg 0 total done left right)
  | succ pairs ih =>
    have h1 := Timed.single (by rfl : raw.halted (0 : Fin 3)=false)
      (left_step total done left right (by omega))
    have h2 := Timed.single (by rfl : raw.halted (1 : Fin 3)=false)
      (right_step total (done+1) (left+1) right (by omega))
    have ht := ih (done+1+1) (left+1) (right+1) (by omega)
    have h := h1.trans (h2.trans ht)
    convert h using 1 <;> congr 1 <;> omega

theorem raw_run (n : ℕ) :
    ∃ r : ExecutionReceipt 3 3,run raw (n+1) ![List.replicate n true,[],[]]=some r ∧
      r.final.tapes=![List.replicate n true,List.replicate ((n+1)/2) true,List.replicate (n/2) true] ∧
      r.steps=n+1 := by
  have hc := cycles (n/2) n 0 0 0 (by omega)
  simp only [Nat.zero_add] at hc
  have hstart : cfg 0 n 0 0 0=initialConfiguration raw ![List.replicate n true,[],[]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  have hfull : Timed raw (n+1) (cfg 0 n 0 0 0) (cfg 2 n n ((n+1)/2) (n/2)) := by
    by_cases he : n%2=0
    · have hn : 2*(n/2)=n := by omega
      have hh : (n+1)/2=n/2 := by omega
      rw [hn] at hc
      have h := hc.trans (Timed.single (by rfl : raw.halted (0 : Fin 3)=false)
        (finish_step 0 (by decide) n (n/2) (n/2)))
      simpa only [hh] using h
    · have hn : 2*(n/2)+1=n := by omega
      have hh : (n+1)/2=n/2+1 := by omega
      have h1 := Timed.single (by rfl : raw.halted (0 : Fin 3)=false)
        (left_step n (2*(n/2)) (n/2) (n/2) (by omega))
      rw [hn] at h1
      have h := hc.trans (h1.trans (Timed.single (by rfl : raw.halted (1 : Fin 3)=false)
        (finish_step 1 (by decide) n (n/2+1) (n/2))))
      have ht : 2*(n/2)+(1+1)=n+1 := by omega
      simpa only [ht,hh] using h
  rw [hstart] at hfull
  obtain ⟨r,hr,hf,hs⟩ := hfull.run (by rfl)
  exact ⟨r,hr,by rw [hf]; rfl,hs⟩

def machine : Machine 4 5 := Rewind.machine raw

theorem split_run (n : ℕ) :
    ClockJoin.ReadyRun machine (2*n+4) ![List.replicate n true,[],[],[]]
      ![List.replicate n true,List.replicate ((n+1)/2) true,List.replicate (n/2) true,
        List.replicate (n+1) false] := by
  obtain ⟨base,hr,ht,hs⟩ := raw_run n
  obtain ⟨r,hrun,hbase,hcap,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hr 0
  have he : 2*base.steps+2=2*n+4 := by omega
  rw [he] at hrun hsteps
  refine ⟨r,?_,?_,hh,hsteps.le⟩
  · convert hrun using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i
    fin_cases i
    · exact (hbase 0).trans (congrFun ht 0)
    · exact (hbase 1).trans (congrFun ht 1)
    · exact (hbase 2).trans (congrFun ht 2)
    · simpa [hs] using hcap

end NearCubicWires.RepairOrdinary.PCPUnarySplit
