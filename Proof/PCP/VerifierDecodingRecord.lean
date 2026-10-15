import Proof.PCP.VerifierDecodingRecordFields

/-! The complete existing seven-node validator, from its real start control.
Both reused flags are cleared; missing presence and malformed fields halt
false. Only successful records promise the next reusable streaming endpoint. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.RecordMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def recordValid (bits bound : List Bool) (t : ℕ) : Bool :=
  match bits with
  | [] => false
  | present::rest => if present then presentValid rest bound t else absentValid rest bound.length t

def backingAfter (bits backing bound : List Bool) : List Bool :=
  match bits with
  | true::rest => frame (rest.take bound.length)
  | _ => backing

theorem clear_prefix (source backing bound : List Bool) (pos j t cap : ℕ)
    (rangeFlag result : Bool) :
    Timed machine 2 (cfg machine.start source backing bound pos j t cap rangeFlag result)
      (cfg (RecoveryCalls.code sizes 1 (programs 1).start)
        source backing bound pos j t cap false false) := by
  obtain ⟨r,hr,hf,hs⟩ := clear_run source backing bound pos j t cap rangeFlag result
  have hp := call_prefix 0 1 1 _ r hr (by rfl)
  rw [hf,hs] at hp
  exact hp

theorem presence_prefix (pre bits backing bound : List Bool) (j t cap : ℕ) (bit : Bool) :
    ∃ n, n≤4 ∧ Timed machine n
      (cfg (RecoveryCalls.code sizes 1 (programs 1).start)
        (pre++frame (bit::bits)) backing bound pre.length j t cap false false)
      (cfg (RecoveryCalls.code sizes (if bit then 2 else 3) (programs (if bit then 2 else 3)).start)
        (pre++frame (bit::bits)) backing bound (pre.length+2) j t cap false false) := by
  obtain ⟨r,hr,hf,hs⟩ := presence_run pre (bit::bits) backing bound j t cap false false
  have hn : next 1 r.final.control r.final.scanned=some (if bit then 2 else 3) := by
    cases bit <;> simp [next,hf,presenceOutput,cfg,TagMachine.received,TagMachine.extend]
  have hp := call_prefix 1 (if bit then 2 else 3) 3 _ r hr hn
  rw [hf] at hp
  refine ⟨r.steps+1,by omega,?_⟩
  have hstart : (programs 1).start=presenceProgram.start := rfl
  cases bit <;> simpa [presenceOutput,controlConfig,RecoveryCalls.restarted,cfg,hstart] using hp

theorem record_run (pre bits backing bound : List Bool) (t cap : ℕ)
    (rangeFlag result : Bool)
    (hb : backing.length≤2*bound.length+1) (hc : 2*bound.length+1≤cap) :
    ∃ r, runFrom machine (8*bound.length+12*t+30)
        (cfg machine.start (pre++frame bits) backing bound pre.length bound.length t cap rangeFlag result)=some r ∧
      r.steps≤8*bound.length+12*t+30 ∧ r.final.scanned 7=recordValid bits bound t ∧
      (recordValid bits bound t=true →
        r.final=cfg (RecoveryCalls.controlCode sizes none)
          (pre++frame bits) (backingAfter bits backing bound) bound
          (pre.length+2*(1+bound.length+4*t)) bound.length t cap (bits.headD false) true) := by
  have hclear := clear_prefix (pre++frame bits) backing bound pre.length bound.length t cap rangeFlag result
  cases bits with
  | nil =>
    obtain ⟨base,hr,hf,hs⟩ := presence_run pre [] backing bound bound.length t cap false false
    have hn : next 1 base.final.control base.final.scanned=none := by
      simp [next,hf,presenceOutput,cfg]
    have hp := stop_prefix 1 3 _ base hr hn
    obtain ⟨r,hrun,hfinal,hsteps⟩ := bounded_run (hclear.trans hp)
      (show 2+(base.steps+1)≤8*bound.length+12*t+30 by omega)
      (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
    refine ⟨r,hrun,hsteps,?_,by simp [recordValid]⟩
    apply false_result
    simp [hfinal,RecoveryCalls.stopped,hf,presenceOutput,cfg]
  | cons bit bits =>
    obtain ⟨n,hn,hpresence⟩ := presence_prefix pre bits backing bound bound.length t cap bit
    have hprefix := hclear.trans hpresence
    have he : (pre++Streaming.marks [bit])++frame bits=pre++frame (bit::bits) := by
      rw [List.append_assoc,←Streaming.frame_append]
      rfl
    have hl : (pre++Streaming.marks [bit]).length=pre.length+2 := by
      simp [Streaming.marks_length]
    have hpos : pre.length+2+2*bound.length+8*t=pre.length+2*(1+bound.length+4*t) := by omega
    cases bit with
    | false =>
      obtain ⟨tail,ht,hts,hvalid,hout⟩ := absent_field_tail
        (pre++Streaming.marks [false]) bits backing bound bound.length t cap
      rw [he,hl] at ht hout
      rw [hpos] at hout
      obtain ⟨r,hrun,hfinal,hsteps⟩ := prepend_run hprefix tail ht
        (show 2+n+tail.steps≤8*bound.length+12*t+30 by omega)
      refine ⟨r,hrun,hsteps,?_,?_⟩
      · simpa only [hfinal,recordValid,Bool.false_eq_true,↓reduceIte] using hvalid
      · intro h
        exact hfinal.trans (hout h)
    | true =>
      obtain ⟨tail,ht,hts,hvalid,hout⟩ := present_field_tail
        (pre++Streaming.marks [true]) bits backing bound t cap hb hc
      rw [he,hl] at ht hout
      rw [hpos] at hout
      obtain ⟨r,hrun,hfinal,hsteps⟩ := prepend_run hprefix tail ht
        (show 2+n+tail.steps≤8*bound.length+12*t+30 by omega)
      refine ⟨r,hrun,hsteps,?_,?_⟩
      · simpa only [hfinal,recordValid,↓reduceIte] using hvalid
      · intro h
        exact hfinal.trans (hout h)

end NearCubicWires.RepairSource.VerifierDecoding.RecordMachine
