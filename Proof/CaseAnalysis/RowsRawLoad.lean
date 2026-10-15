import Proof.CaseAnalysis.RowsCapacityBudget

/-! Sequential native packet loading. The raw field is copied once and
only its target/counter are rewound; the packet cursor advances. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawLoad
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (q : Fin 4) (sourceMove targetMove counterMove : HeadMove)
    (targetWrite counterWrite : Option Bool) : Action 3 4 :=
  ⟨q,![none,targetWrite,counterWrite],![sourceMove,targetMove,counterMove]⟩
def machine : Machine 3 4 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==3
  rule := fun q scanned=>if q=0 then
      if scanned 0 then some (action 1 .right .stay .stay none none)
      else some (action 2 .right .stay .left none none)
    else if q=1 then some (action 0 .right .right .right (some (scanned 0)) (some true))
    else if q=2 then
      if scanned 2 then some (action 2 .stay .left .left none (some false))
      else some (action 3 .stay .stay .stay none none)
    else none
def scan (q : Fin 4) (source : List Bool) (pos : ℕ) (out : List Bool) : Configuration 3 4 :=
  ⟨q,![pos,out.length,out.length],![source,out,List.replicate out.length true]⟩
def reset (q : Fin 4) (source : List Bool) (pos : ℕ) (out : List Bool) (k z : ℕ) : Configuration 3 4 :=
  ⟨q,![pos,k,k-1],![source,out,List.replicate k true++List.replicate z false]⟩

theorem mark_step (pre tail out : List Bool) :
    step machine (scan 0 (pre++true::tail) pre.length out)=
      some (scan 1 (pre++true::tail) (pre.length+1) out) := by
  simp [step,machine,scan,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action]

theorem bit_step (pre tail out : List Bool) (b : Bool) :
    step machine (scan 1 (pre++b::tail) pre.length out)=
      some (scan 0 (pre++b::tail) (pre.length+1) (out++[b])) := by
  simp [step,machine,scan,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action,Streaming.write_append,List.replicate_add]

theorem end_step (pre tail out : List Bool) :
    step machine (scan 0 (pre++false::tail) pre.length out)=
      some (reset 2 (pre++false::tail) (pre.length+1) out out.length 0) := by
  simp [step,machine,scan,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,reset,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action,reset]

theorem rewind_step (source out : List Bool) (pos k z : ℕ) :
    step machine (reset 2 source pos out (k+1) z)=some (reset 2 source pos out k (z+1)) := by
  simp [step,machine,reset,Configuration.scanned,Streaming.read_counter]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action,Streaming.erase_counter]

theorem stop_step (source out : List Bool) (pos z : ℕ) :
    step machine (reset 2 source pos out 0 z)=some (reset 3 source pos out 0 z) := by
  simp [step,machine,reset,Configuration.scanned,Streaming.read_zeros]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action]

theorem rewind_time (source out : List Bool) (pos k z : ℕ) :
    Timed machine (k+1) (reset 2 source pos out k z) (reset 3 source pos out 0 (k+z)) := by
  induction k generalizing z with
  | zero => simpa using Timed.single (by rfl) (stop_step source out pos z)
  | succ k ih =>
    have ht := Timed.step (by rfl) (rewind_step source out pos k z) (ih (z+1))
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

theorem scan_time (pre bits tail out : List Bool) :
    Timed machine (2*bits.length+1) (scan 0 (pre++frame bits++tail) pre.length out)
      (reset 2 (pre++frame bits++tail) (pre.length+2*bits.length+1) (out++bits) (out++bits).length 0) := by
  induction bits generalizing pre out with
  | nil => simpa [frame] using Timed.single (by rfl) (end_step pre tail out)
  | cons b bits ih =>
    have ht := ih (pre++[true,b]) (out++[b])
    have hb := bit_step (pre++[true]) (frame bits++tail) out b
    have hm := mark_step pre (b::frame bits++tail) out
    have he : (pre++[true,b])++frame bits++tail=pre++frame (b::bits)++tail := by
      simp [frame,List.append_assoc]
    rw [he] at ht
    have ht' : Timed machine (2*bits.length+1)
        (scan 0 (pre++frame (b::bits)++tail) (pre.length+2) (out++[b]))
        (reset 2 (pre++frame (b::bits)++tail) (pre.length+2*(b::bits).length+1)
          (out++b::bits) (out++b::bits).length 0) := by
      simpa [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_add] using ht
    have hb' : step machine (scan 1 (pre++frame (b::bits)++tail) (pre.length+1) out)=
        some (scan 0 (pre++frame (b::bits)++tail) (pre.length+2) (out++[b])) := by
      simpa [frame,List.append_assoc,Nat.add_assoc] using hb
    have hm' : step machine (scan 0 (pre++frame (b::bits)++tail) pre.length out)=
        some (scan 1 (pre++frame (b::bits)++tail) (pre.length+1) out) := by
      simpa [frame,List.append_assoc] using hm
    have h := Timed.step (by rfl) hm' (Timed.step (by rfl) hb' ht')
    simpa [Nat.mul_add,Nat.add_assoc] using h

theorem field_run (pre bits tail : List Bool) :
    ∃ r,runFrom machine (3*bits.length+2) (scan 0 (pre++frame bits++tail) pre.length [])=some r ∧
      r.final=reset 3 (pre++frame bits++tail) (pre.length+2*bits.length+1) bits 0 bits.length ∧
      r.steps=3*bits.length+2 := by
  have hs := scan_time pre bits tail []
  simp only [List.nil_append] at hs
  have ht := rewind_time (pre++frame bits++tail) bits (pre.length+2*bits.length+1) bits.length 0
  have hall := hs.trans ht
  have he : 2*bits.length+1+(bits.length+1)=3*bits.length+2 := by omega
  rw [he,Nat.add_zero] at hall
  exact hall.run (by rfl)

end NearCubicWires.RepairOrdinary.CloseoutRowsRawLoad
