import Proof.PCP.PCPStackReady

/-! Push a physical unary count directly as a reversed unary framed field.
No numeric binary conversion or prebuilt framed copy is used. -/
namespace NearCubicWires.RepairOrdinary.PCPUnaryStackPush
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (q : Fin 4) (bit : Bool) (sourceMove : HeadMove) : Action 2 4 :=
  ⟨q,![none,some bit],![sourceMove,.right]⟩
def raw : Machine 2 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==3
  rule := fun q bits => if q.val=0 then some (action 1 false .stay)
    else if q.val=1 then if bits 0 then some (action 2 true .stay)
      else some ⟨3,fun _ => none,fun _ => .stay⟩
    else if q.val=2 then some (action 1 true .right) else none
def cfg (q : Fin 4) (total done : ℕ) (stack : List Bool) : Configuration 2 4 :=
  ⟨q,![done,stack.length],![List.replicate total true,stack]⟩

theorem write_step (q next : Fin 4) (total done : ℕ) (stack : List Bool)
    (bit : Bool) (move : HeadMove)
    (hr : raw.rule q (cfg q total done stack).scanned=some (action next bit move)) :
    step raw (cfg q total done stack)=some (cfg next total (move.apply done) (stack++[bit])) := by
  simp only [step,cfg] at hr ⊢
  rw [hr]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i
    fin_cases i
    · rfl
    · simpa [applyAction,cfg,action] using Streaming.write_append stack bit

theorem first_step (total done : ℕ) (stack : List Bool) (hd : done<total) :
    step raw (cfg 1 total done stack)=some (cfg 2 total done (stack++[true])) := by
  have hb : readTapeBit (List.replicate total true) done=true := by simp [readTapeBit,List.getD,hd]
  exact write_step 1 2 total done stack true .stay (by simp [raw,cfg,Configuration.scanned,hb])

theorem second_step (total done : ℕ) (stack : List Bool) :
    step raw (cfg 2 total done stack)=some (cfg 1 total (done+1) (stack++[true])) :=
  write_step 2 1 total done stack true .right (by rfl)

theorem finish_step (total : ℕ) (stack : List Bool) :
    step raw (cfg 1 total total stack)=some (cfg 3 total total stack) := by
  have hb : readTapeBit (List.replicate total true) total=false := by simp [readTapeBit,List.getD]
  simp [step,raw,cfg,Configuration.scanned,hb]
  rfl

theorem count_loop (remaining total done : ℕ) (stack : List Bool) (hn : done+remaining=total) :
    Timed raw (2*remaining+1) (cfg 1 total done stack)
      (cfg 3 total total (stack++List.replicate (2*remaining) true)) := by
  induction remaining generalizing done stack with
  | zero =>
    have hd : done=total := by omega
    subst done
    simpa using Timed.single (by rfl : raw.halted (1 : Fin 4)=false) (finish_step total stack)
  | succ remaining ih =>
    have h1 := Timed.single (by rfl : raw.halted (1 : Fin 4)=false)
      (first_step total done stack (by omega))
    have h2 := Timed.single (by rfl : raw.halted (2 : Fin 4)=false)
      (second_step total done (stack++[true]))
    have ht := ih (done+1) (stack++[true]++[true]) (by omega)
    have h := h1.trans (h2.trans ht)
    have he : (stack++[true]++[true])++List.replicate (2*remaining) true=
        stack++List.replicate (2*(remaining+1)) true := by
      have hr := List.replicate_add 2 (2*remaining) true
      have hn : 2+2*remaining=2*(remaining+1) := by omega
      rw [hn] at hr
      simp only [List.append_assoc]
      exact congrArg (List.append stack) hr.symm
    have htime : 1+(1+(2*remaining+1))=2*(remaining+1)+1 := by omega
    rw [he,htime] at h
    exact h

theorem frame_unary (n : ℕ) : frame (List.replicate n true)=List.replicate (2*n) true++[false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    change true::true::frame (List.replicate n true)=_
    rw [ih]
    have he : 2*(n+1)=2+2*n := by omega
    rw [he,List.replicate_add]
    rfl

theorem raw_run (n : ℕ) (stack : List Bool) :
    ∃ r : ExecutionReceipt 2 4,runFrom raw (2*n+2) (cfg 0 n 0 stack)=some r ∧
      r.final=cfg 3 n n (stack++(frame (List.replicate n true)).reverse) ∧ r.steps=2*n+2 := by
  have hi := write_step 0 1 n 0 stack false .stay (by rfl)
  have ht := count_loop n n 0 (stack++[false]) (by omega)
  have h := (Timed.single (by rfl : raw.halted (0 : Fin 4)=false) hi).trans ht
  have he : (stack++[false])++List.replicate (2*n) true=
      stack++(frame (List.replicate n true)).reverse := by simp [frame_unary,List.append_assoc]
  rw [he] at h
  have htime : 1+(2*n+1)=2*n+2 := by omega
  rw [htime] at h
  exact h.run (by rfl)

def selected (i : Fin 2) : Bool := decide (i=0)
def machine : Machine 3 6 := MaskedReset.machine raw selected
def entry (n : ℕ) (stack : List Bool) := Rewind.recording (cfg 0 n 0 stack) 0

theorem push_run (n : ℕ) (stack : List Bool) :
    ∃ r : ExecutionReceipt 3 6,runFrom machine (4*n+6) (entry n stack)=some r ∧
      r.final.tapes=![List.replicate n true,stack++(frame (List.replicate n true)).reverse,
        List.replicate (2*n+2) false] ∧
      r.final.heads=![0,stack.length+2*n+1,0] ∧ r.steps=4*n+6 := by
  obtain ⟨base,hr,hf,hs⟩ := raw_run n stack
  have hhead : ∀ i,selected i=true → base.final.heads i ≤ base.steps := by
    intro i hi
    have he : i=0 := by simpa [selected] using hi
    subst i
    rw [hf,hs]
    change n ≤ 2*n+2
    omega
  obtain ⟨r,hrun,hfinal,hsteps,_⟩ := MaskedReset.reset_run raw selected _ _ base hr hhead
  have he : 2*base.steps+2=4*n+6 := by omega
  rw [he] at hrun hsteps
  refine ⟨r,hrun,?_,?_,hsteps⟩
  · rw [hfinal,hf,hs]
    funext i
    fin_cases i <;> rfl
  · rw [hfinal,hf]
    funext i
    fin_cases i
    · rfl
    · change (stack++(frame (List.replicate n true)).reverse).length=stack.length+2*n+1
      simp [frame_length]; omega
    · rfl

end NearCubicWires.RepairOrdinary.PCPUnaryStackPush
