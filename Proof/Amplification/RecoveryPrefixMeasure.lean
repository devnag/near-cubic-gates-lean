import Proof.Amplification.RecoveryPrefixLoop

/-! One streaming pass over the two actual search fields produces both the
raw capacity argument and the literal sentinel repetition driver. The first
field's payload bits are counted; the second field is the requested unary
prefix length. No numeric parameter selects the finite machine. -/
namespace NearCubicWires.RepairSource.RecoveryPrefixMeasure
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (q : Fin 12) (sourceMove : HeadMove) (number driver : Option Bool) : Action 3 12 :=
  ⟨q,![none,number,driver],![sourceMove,if number.isSome then .right else .stay,
    if driver.isSome then .right else .stay]⟩
def raw : Machine 3 12 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val=11
  rule := fun q bits=>match q.val with
    | 0 => some (action 1 .stay none (some false))
    | 1 => some (action 2 .stay (some true) none)
    | 2 => some (action 3 .stay (some true) none)
    | 3 => some (action 4 .stay (some true) none)
    | 4 => some (action 5 .stay (some true) none)
    | 5 => some (if bits 0 then action 6 .right none none else action 8 .right none none)
    | 6 => some (action 5 .right (some true) none)
    | 8 => some (if bits 0 then action 9 .right none none else action 11 .stay none none)
    | 9 => some (action 10 .right (some true) (some true))
    | 10 => some (action 8 .stay (some true) none)
    | _ => none

def cfg (q : Fin 12) (source : List Bool) (pos n done : Nat) : Configuration 3 12 :=
  ⟨q,![pos,n,done+1],![source,List.replicate n true,VerifierDecoding.CompareMachine.word done]⟩

theorem boot_first (source : List Bool) :
    step raw (initialConfiguration raw ![source,[],[]])=some (cfg 1 source 0 0 0) := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem boot_step (source : List Bool) (n : Nat) (hn : n<4) :
    step raw (cfg ⟨n+1,by omega⟩ source 0 n 0)=some (cfg ⟨n+2,by omega⟩ source 0 (n+1) 0) := by
  interval_cases n
  all_goals apply congrArg some
  all_goals apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> rfl)

theorem boot_tail (source : List Bool) (remaining n : Nat) (hn : n+remaining=4) :
    Timed raw remaining (cfg ⟨n+1,by omega⟩ source 0 n 0) (cfg 5 source 0 4 0) := by
  induction remaining generalizing n with
  | zero =>
    have he : n=4 := by omega
    subst n
    exact .refl _ _
  | succ remaining ih =>
    exact Timed.step (by simp [raw,cfg]; omega) (boot_step source n (by omega))
      (ih (n+1) (by omega))

theorem boot_trace (source : List Bool) : Timed raw 5
    (initialConfiguration raw ![source,[],[]]) (cfg 5 source 0 4 0) :=
  Timed.step (by rfl) (boot_first source) (boot_tail source 4 0 rfl)

theorem marker_step (pre tail : List Bool) (n done : Nat) :
    step raw (cfg 5 (pre++true::tail) pre.length n done)=
      some (cfg 6 (pre++true::tail) (pre.length+1) n done) := by
  simp only [step,raw,cfg,Configuration.scanned,Matrix.cons_val_zero,Streaming.read_append,↓reduceIte]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action]

theorem payload_step (source : List Bool) (pos n done : Nat) :
    step raw (cfg 6 source pos n done)=some (cfg 5 source (pos+1) (n+1) done) := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i
    · rfl
    · change writeTapeBit (List.replicate n true) n true=List.replicate (n+1) true
      simpa only [List.length_replicate,List.replicate_add,List.replicate_one] using
        Streaming.write_append (List.replicate n true) true
    · rfl

theorem payload_trace (bits pre tail : List Bool) (n done : Nat) :
    Timed raw (2*bits.length)
      (cfg 5 (pre++frame bits++tail) pre.length n done)
      (cfg 5 (pre++frame bits++tail) (pre.length+2*bits.length) (n+bits.length) done) := by
  induction bits generalizing pre n with
  | nil => simpa using Timed.refl raw (cfg 5 (pre++frame []++tail) pre.length n done)
  | cons bit bits ih =>
    let source := pre++frame (bit::bits)++tail
    have he : (pre++[true,bit])++frame bits++tail=source := by simp [source,RepairOrdinary.frame,List.append_assoc]
    have ht := ih (pre++[true,bit]) (n+1)
    rw [he] at ht
    have hm := marker_step pre (bit::(frame bits++tail)) n done
    have hp := payload_step source (pre.length+1) n done
    have ht' : Timed raw (2*bits.length)
        (cfg 5 source (pre.length+2) (n+1) done)
        (cfg 5 source (pre.length+2*(bit::bits).length) (n+(bit::bits).length) done) := by
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_add] using ht
    have hm' : step raw (cfg 5 source pre.length n done)=some (cfg 6 source (pre.length+1) n done) := by
      simpa [source,RepairOrdinary.frame,List.append_assoc] using hm
    have hall := Timed.step (by rfl) hm' (Timed.step (by rfl) hp ht')
    rw [show 2*bits.length+1+1=2*(bit::bits).length by simp only [List.length_cons]; omega] at hall
    exact hall

theorem separator_step (pre tail : List Bool) (n done : Nat) :
    step raw (cfg 5 (pre++false::tail) pre.length n done)=
      some (cfg 8 (pre++false::tail) (pre.length+1) n done) := by
  simp only [step,raw,cfg,Configuration.scanned,Matrix.cons_val_zero,Streaming.read_append]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action]

theorem driver_marker (pre tail : List Bool) (n done : Nat) :
    step raw (cfg 8 (pre++true::tail) pre.length n done)=
      some (cfg 9 (pre++true::tail) (pre.length+1) n done) := by
  simp only [step,raw,cfg,Configuration.scanned,Matrix.cons_val_zero,Streaming.read_append,↓reduceIte]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action]

theorem driver_payload (source : List Bool) (pos n done : Nat) :
    step raw (cfg 9 source pos n done)=some (cfg 10 source (pos+1) (n+1) (done+1)) := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i
    · rfl
    · change writeTapeBit (List.replicate n true) n true=List.replicate (n+1) true
      simpa only [List.length_replicate,List.replicate_add,List.replicate_one] using
        Streaming.write_append (List.replicate n true) true
    · change writeTapeBit (false::List.replicate done true) (done+1) true=false::List.replicate (done+1) true
      simpa only [List.length_cons,List.length_replicate,List.replicate_add,List.replicate_one,List.cons_append] using
        Streaming.write_append (false::List.replicate done true) true

theorem driver_double (source : List Bool) (pos n done : Nat) :
    step raw (cfg 10 source pos n done)=some (cfg 8 source pos (n+1) done) := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i
    · rfl
    · change writeTapeBit (List.replicate n true) n true=List.replicate (n+1) true
      simpa only [List.length_replicate,List.replicate_add,List.replicate_one] using
        Streaming.write_append (List.replicate n true) true
    · rfl

theorem driver_trace (remaining : Nat) (pre tail : List Bool) (n done : Nat) :
    Timed raw (3*remaining)
      (cfg 8 (pre++frame (List.replicate remaining true)++tail) pre.length n done)
      (cfg 8 (pre++frame (List.replicate remaining true)++tail) (pre.length+2*remaining)
        (n+2*remaining) (done+remaining)) := by
  induction remaining generalizing pre n done with
  | zero => simpa using Timed.refl raw (cfg 8 (pre++frame []++tail) pre.length n done)
  | succ remaining ih =>
    let source := pre++frame (List.replicate (remaining+1) true)++tail
    have he : (pre++[true,true])++frame (List.replicate remaining true)++tail=source := by
      simp [source,List.replicate_succ,RepairOrdinary.frame,List.append_assoc]
    have ht := ih (pre++[true,true]) (n+2) (done+1)
    rw [he] at ht
    have hm := driver_marker pre (true::(frame (List.replicate remaining true)++tail)) n done
    have hp := driver_payload source (pre.length+1) n done
    have hd := driver_double source (pre.length+2) (n+1) (done+1)
    have ht' : Timed raw (3*remaining) (cfg 8 source (pre.length+2) (n+2) (done+1))
        (cfg 8 source (pre.length+2*(remaining+1)) (n+2*(remaining+1)) (done+(remaining+1))) := by
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_add] using ht
    have hm' : step raw (cfg 8 source pre.length n done)=some (cfg 9 source (pre.length+1) n done) := by
      simpa [source,List.replicate_succ,RepairOrdinary.frame,List.append_assoc] using hm
    have hall := Timed.step (by rfl) hm' (Timed.step (by rfl) hp (Timed.step (by rfl) hd ht'))
    rw [show 3*remaining+1+1+1=3*(remaining+1) by omega] at hall
    exact hall

theorem finish (pre tail : List Bool) (n done : Nat) :
    step raw (cfg 8 (pre++false::tail) pre.length n done)=some (cfg 11 (pre++false::tail) pre.length n done) := by
  simp only [step,raw,cfg,Configuration.scanned,Matrix.cons_val_zero,Streaming.read_append]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action]

end NearCubicWires.RepairSource.RecoveryPrefixMeasure
