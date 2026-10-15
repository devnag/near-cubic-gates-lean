import Proof.PCP.VerifierDecodingReadyCounters

/-! Four actual output marks per input tape-count mark. The finite control
is fixed, and the source is the decoder's already produced capped t counter. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.Fourfold
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def successor : Fin 5 → Fin 5 := ![1,2,3,0,4]
def emit (q : Fin 5) : Action 2 5 :=
  ⟨successor q,![none,some true],![if q=0 then .right else .stay,.right]⟩
def machine : Machine 2 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val=4
  rule := fun q bits => if q.val<4 then
    if q=0 ∧ bits 0=false then some ⟨4,fun _ => none,fun _ => .stay⟩ else some (emit q)
    else none
def cfg (q : Fin 5) (c t pos count : ℕ) : Configuration 2 5 :=
  ⟨q,![pos+1,count+1],![CapMachine.counter c t,CompareMachine.word count]⟩

theorem word_write (count : ℕ) :
    writeTapeBit (CompareMachine.word count) (count+1) true=CompareMachine.word (count+1) := by
  have h := Streaming.write_append (false::List.replicate count true) true
  simpa [CompareMachine.word,List.replicate_add] using h

theorem enter_step (c t pos count : ℕ) (h : pos<t) :
    step machine (cfg 0 c t pos count)=some (cfg 1 c t (pos+1) (count+1)) := by
  simp [step,machine,cfg,Configuration.scanned,CapMachine.counter_read,h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,emit,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,emit,word_write]

theorem emit_step (q : Fin 5) (hq : 1≤q.val) (hmax : q.val≤3) (c t pos count : ℕ) :
    step machine (cfg q c t pos count)=some (cfg (successor q) c t pos (count+1)) := by
  have hq0 : q≠0 := by intro h; subst q; simp at hq
  simp [step,machine,cfg,hq0,show q.val<4 by omega]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,emit,HeadMove.apply,hq0]
  · funext i; fin_cases i <;> simp [applyAction,emit,word_write]

theorem stop_step (c t count : ℕ) :
    step machine (cfg 0 c t t count)=some (cfg 4 c t t count) := by
  simp [step,machine,cfg,Configuration.scanned,CapMachine.counter_read]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem round (c t pos count : ℕ) (h : pos<t) :
    Timed machine 4 (cfg 0 c t pos count) (cfg 0 c t (pos+1) (count+4)) := by
  have a := Timed.single (by rfl : machine.halted (0 : Fin 5)=false) (enter_step c t pos count h)
  have b := Timed.single (by rfl : machine.halted (1 : Fin 5)=false) (emit_step 1 (by decide) (by decide) c t (pos+1) (count+1))
  have d := Timed.single (by rfl : machine.halted (2 : Fin 5)=false) (emit_step 2 (by decide) (by decide) c t (pos+1) (count+2))
  have e := Timed.single (by rfl : machine.halted (3 : Fin 5)=false) (emit_step 3 (by decide) (by decide) c t (pos+1) (count+3))
  exact a.trans (b.trans (d.trans e))

theorem repeat_prefix (n c t pos count : ℕ) (h : pos+n≤t) :
    Timed machine (4*n) (cfg 0 c t pos count) (cfg 0 c t (pos+n) (count+4*n)) := by
  induction n generalizing pos count with
  | zero => simpa using Timed.refl machine (cfg 0 c t pos count)
  | succ n ih =>
    have hp := (round c t pos count (by omega)).trans (ih (pos+1) (count+4) (by omega))
    convert hp using 1 <;> congr 1 <;> omega

theorem fourfold_run (c t : ℕ) :
    ∃ r, runFrom machine (4*t+1) (cfg 0 c t 0 0)=some r ∧
      r.final=cfg 4 c t t (4*t) ∧ r.steps=4*t+1 := by
  have hp := repeat_prefix t c t 0 0 (by omega)
  simp only [Nat.zero_add] at hp
  have ht := Timed.single (by rfl : machine.halted (0 : Fin 5)=false) (stop_step c t (4*t))
  exact (hp.trans ht).run (by rfl)

end NearCubicWires.RepairSource.VerifierDecoding.Fourfold
