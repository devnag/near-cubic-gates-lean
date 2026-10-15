import Proof.MachineModel.UWitnessChoiceKernel

/-! One finite guarded binary-counted prefix controller. Both the complete
prefix and every possible short-prefix rejection are executions of this
same controller. -/
namespace NearCubicWires.RepairOrdinary.UWitnessChoices
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

@[simp] theorem config_control {s : ℕ} (state : Fin s) (w counter bound cap : ℕ) (flag : Bool)
    (source out : List Bool) (cursor : ℕ) (accepted : Bool) :
    (config state w counter bound cap flag source out cursor accepted).control=state := rfl
@[simp] theorem config_heads {s : ℕ} (state : Fin s) (w counter bound cap : ℕ) (flag : Bool)
    (source out : List Bool) (cursor : ℕ) (accepted : Bool) :
    (config state w counter bound cap flag source out cursor accepted).heads=![0,0,0,0,cursor,out.length,0] := by
  funext i; fin_cases i <;> rfl
@[simp] theorem config_tapes {s : ℕ} (state : Fin s) (w counter bound cap : ℕ) (flag : Bool)
    (source out : List Bool) (cursor : ℕ) (accepted : Bool) :
    (config state w counter bound cap flag source out cursor accepted).tapes=
      ![frame (binary w counter),frame (binary w bound),[flag],List.replicate cap false,source,out,[accepted]] := by
  funext i; fin_cases i <;> rfl

def clear : Machine 7 2 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==1
  rule := fun s _ => if s.val=0 then some ⟨1,
    fun i => if i.val=2 ∨ i.val=6 then some false else none,fun _ => .stay⟩ else none
def sizes : Fin 4 → ℕ := ![2,12,4,2]
def programs : (j : Fin 4) → Machine 7 (sizes j)
  | ⟨0,_⟩ => clear
  | ⟨1,_⟩ => check
  | ⟨2,_⟩ => copy
  | ⟨3,_⟩ => close
  | ⟨n+4,h⟩ => False.elim (by omega)
def next (j : Fin 4) (q : Fin (sizes j)) (scan : Fin 7 → Bool) : Option (Fin 4) :=
  if j.val=0 then some 1 else if j.val=1 then some (if scan 2 then 2 else 3)
  else if j.val=2 then if q.val=2 then some 1 else none else none
noncomputable def raw := RecoveryCalls.machine sizes programs 0 next
def loopBudget (w n : ℕ) := (n+1)*(8*w+12)
noncomputable def atCheck (w counter bound cap : ℕ) (source out : List Bool) (cursor : ℕ) :=
  controlConfig (RecoveryCalls.code sizes 1)
    (config check.start w counter bound cap false source out cursor false)
noncomputable def done (w counter bound cap : ℕ) (flag accepted : Bool)
    (source out : List Bool) (cursor : ℕ) :=
  RecoveryCalls.stopped sizes
    (config (0 : Fin 1) w counter bound cap flag source out cursor accepted).heads
    (config (0 : Fin 1) w counter bound cap flag source out cursor accepted).tapes

theorem valid_loop (w counter bound cap : ℕ) (pre bits suffix out : List Bool)
    (hremaining : counter+bits.length=bound) (hbound : bound+1 < 2^w) (hcap : 2*w+1 ≤ cap) :
    ∃ n,n ≤ loopBudget w bits.length ∧
      Timed raw n (atCheck w counter bound cap (pre++frame (bits++suffix)) out pre.length)
        (done w (bound+1) bound cap false true (pre++frame (bits++suffix))
          (out++frame bits) (pre.length+2*bits.length)) := by
  induction bits generalizing counter pre out with
  | nil =>
    have hc : counter=bound := by simpa using hremaining
    subst counter
    obtain ⟨r,hr,hf⟩ := check_run w bound bound cap (pre++frame suffix) out pre.length hbound (by omega) hcap
    have hnext : next 1 r.final.control r.final.scanned=some 3 := by
      simp [next,hf,config,Configuration.scanned,TapeEmbedding.config,WitnessPrefixBody.config,
        WitnessCounterCheck.config,Fin.addCases,readTapeBit]
    obtain ⟨n,hn,hcheck⟩ := call_receipt sizes programs 0 next 1 3 (8*w+7) _ r hr hnext
    rw [hf] at hcheck
    simp only [show decide (bound+1 ≤ bound)=false by simp] at hcheck
    obtain ⟨r',hr',hf',_⟩ := close_run w (bound+1) bound cap (pre++frame suffix) out pre.length
    obtain ⟨m,hm,hclose⟩ := stop_receipt sizes programs 0 next 3 1 _ r' hr' (by simp [next])
    rw [hf'] at hclose
    have h := hcheck.trans hclose
    change Timed raw (n+m) (atCheck w bound bound cap (pre++frame suffix) out pre.length)
      (done w (bound+1) bound cap false true (pre++frame suffix) (out++[false]) pre.length) at h
    refine ⟨n+m,by dsimp [loopBudget]; omega,?_⟩
    simpa only [List.nil_append,List.length_nil,Nat.mul_zero,Nat.add_zero,frame] using h
  | cons bit bits ih =>
    have hc : counter+1 ≤ bound := by simp only [List.length_cons] at hremaining; omega
    let source := pre++frame ((bit::bits)++suffix)
    obtain ⟨r,hr,hf⟩ := check_run w counter bound cap source out pre.length (by omega) (by omega) hcap
    have hnext : next 1 r.final.control r.final.scanned=some 2 := by
      simp [next,hf,config,Configuration.scanned,TapeEmbedding.config,WitnessPrefixBody.config,
        WitnessCounterCheck.config,Fin.addCases,readTapeBit,hc]
    obtain ⟨n,hn,hcheck⟩ := call_receipt sizes programs 0 next 1 2 (8*w+7) _ r hr hnext
    rw [hf] at hcheck
    simp only [show decide (counter+1 ≤ bound)=true by simp [hc]] at hcheck
    obtain ⟨r',hr',hf',_⟩ := copy_run w (counter+1) bound cap pre (bits++suffix) out bit
    obtain ⟨m,hm,hcopy⟩ := call_receipt sizes programs 0 next 2 1 2 _ r' hr' (by simp [next,hf'])
    rw [hf'] at hcopy
    obtain ⟨l,hl,htail⟩ := ih (counter+1) (pre++[true,bit]) (out++[true,bit])
      (by simp only [List.length_cons] at hremaining; omega)
    have he : (pre++[true,bit])++frame (bits++suffix)=source := by simp [source,frame,List.append_assoc]
    rw [he,show (pre++[true,bit]).length=pre.length+2 by simp] at htail
    have h := (hcheck.trans hcopy).trans htail
    refine ⟨n+m+l,?_,?_⟩
    · dsimp only [loopBudget,List.length_cons] at *
      nlinarith
    · simpa [raw,atCheck,done,RecoveryCalls.restarted,controlConfig,source,frame,List.append_assoc,
        Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem short_loop (w counter bound cap : ℕ) (pre bits out : List Bool)
    (hshort : counter+bits.length < bound) (hbound : bound+1 < 2^w) (hcap : 2*w+1 ≤ cap) :
    ∃ n,n ≤ loopBudget w bits.length ∧
      Timed raw n (atCheck w counter bound cap (pre++frame bits) out pre.length)
        (done w (counter+bits.length+1) bound cap true false (pre++frame bits)
          (out++Streaming.marks bits) (pre.length+2*bits.length)) := by
  induction bits generalizing counter pre out with
  | nil =>
    have hc : counter+1 ≤ bound := by simp only [List.length_nil,Nat.add_zero] at hshort; omega
    obtain ⟨r,hr,hf⟩ := check_run w counter bound cap (pre++frame []) out pre.length (by omega) (by omega) hcap
    have hnext : next 1 r.final.control r.final.scanned=some 2 := by
      simp [next,hf,config,Configuration.scanned,TapeEmbedding.config,WitnessPrefixBody.config,
        WitnessCounterCheck.config,Fin.addCases,readTapeBit,hc]
    obtain ⟨n,hn,hcheck⟩ := call_receipt sizes programs 0 next 1 2 (8*w+7) _ r hr hnext
    rw [hf] at hcheck
    simp only [show decide (counter+1 ≤ bound)=true by simp [hc]] at hcheck
    obtain ⟨r',hr',hf',_⟩ := copy_reject w (counter+1) bound cap pre out
    obtain ⟨m,hm,hcopy⟩ := stop_receipt sizes programs 0 next 2 1 _ r' hr' (by simp [next,hf'])
    rw [hf'] at hcopy
    have h := hcheck.trans hcopy
    change Timed raw (n+m) (atCheck w counter bound cap (pre++frame []) out pre.length)
      (done w (counter+1) bound cap true false (pre++frame []) out pre.length) at h
    refine ⟨n+m,by dsimp [loopBudget]; omega,?_⟩
    simpa only [Streaming.marks,List.flatMap_nil,List.append_nil,List.length_nil,Nat.mul_zero,Nat.add_zero] using h
  | cons bit bits ih =>
    have hc : counter+1 ≤ bound := by simp only [List.length_cons] at hshort; omega
    obtain ⟨r,hr,hf⟩ := check_run w counter bound cap (pre++frame (bit::bits)) out pre.length (by omega) (by omega) hcap
    have hnext : next 1 r.final.control r.final.scanned=some 2 := by
      simp [next,hf,config,Configuration.scanned,TapeEmbedding.config,WitnessPrefixBody.config,
        WitnessCounterCheck.config,Fin.addCases,readTapeBit,hc]
    obtain ⟨n,hn,hcheck⟩ := call_receipt sizes programs 0 next 1 2 (8*w+7) _ r hr hnext
    rw [hf] at hcheck
    simp only [show decide (counter+1 ≤ bound)=true by simp [hc]] at hcheck
    obtain ⟨r',hr',hf',_⟩ := copy_run w (counter+1) bound cap pre bits out bit
    obtain ⟨m,hm,hcopy⟩ := call_receipt sizes programs 0 next 2 1 2 _ r' hr' (by simp [next,hf'])
    rw [hf'] at hcopy
    obtain ⟨l,hl,htail⟩ := ih (counter+1) (pre++[true,bit]) (out++[true,bit])
      (by simp only [List.length_cons] at hshort; omega)
    have he : (pre++[true,bit])++frame bits=pre++frame (bit::bits) := by simp [frame,List.append_assoc]
    rw [he,show (pre++[true,bit]).length=pre.length+2 by simp] at htail
    have h := (hcheck.trans hcopy).trans htail
    refine ⟨n+m+l,?_,?_⟩
    · dsimp only [loopBudget,List.length_cons] at *
      nlinarith
    · simpa [raw,atCheck,done,RecoveryCalls.restarted,controlConfig,Streaming.marks,List.append_assoc,
        Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

end NearCubicWires.RepairOrdinary.UWitnessChoices
