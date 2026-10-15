import Proof.PCP.VerifierDecodingRecordTags

/-! Both complete field/tag branches of the actual record call graph.
Malformed fields reject before dependent work; successful branches consume
exactly j+4t payload bits and retain the enclosing record workspace. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.RecordMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem prepend_run {n fuel budget : ℕ}
    {input middle : Configuration 8 (Fintype.card (RecoveryCalls.Control sizes))}
    (h : Timed machine n input middle)
    (r : ExecutionReceipt 8 (Fintype.card (RecoveryCalls.Control sizes)))
    (hr : runFrom machine fuel middle=some r) (hb : n+r.steps≤budget) :
    ∃ out, runFrom machine budget input=some out ∧ out.final=r.final ∧ out.steps≤budget := by
  obtain ⟨hp,hh⟩ := prefix_of_run machine fuel middle r hr
  exact bounded_run (h.trans ⟨r.peakTapeCells,hp⟩) hb hh

def presentValid (bits bound : List Bool) (t : ℕ) : Bool :=
  decide (rangeValid bits bound) && TagScan.tests 4 (TagMachine.valid true) t (bits.drop bound.length)
def absentValid (bits : List Bool) (j t : ℕ) : Bool :=
  decide (j≤bits.length ∧ bits.take j=List.replicate j false) &&
    TagScan.tests 4 (TagMachine.valid false) t (bits.drop j)

theorem present_field_tail (pre bits backing bound : List Bool) (t cap : ℕ)
    (hb : backing.length≤2*bound.length+1) (hc : 2*bound.length+1≤cap) :
    ∃ r, runFrom machine (8*bound.length+12*t+20)
        (cfg (RecoveryCalls.code sizes 2 (programs 2).start)
          (pre++frame bits) backing bound pre.length bound.length t cap false false)=some r ∧
      r.steps≤8*bound.length+12*t+20 ∧ r.final.scanned 7=presentValid bits bound t ∧
      (presentValid bits bound t=true →
        r.final=cfg (RecoveryCalls.controlCode sizes none)
          (pre++frame bits) (frame (bits.take bound.length)) bound
          (pre.length+2*bound.length+8*t) bound.length t cap true true) := by
  obtain ⟨base,hr,hs,hfalse,hflag,hgood⟩ := range_checked pre bits backing bound t cap hb hc
  by_cases hv : rangeValid bits bound
  · have hfield := hgood hv
    have hn : next 2 base.final.control base.final.scanned=some 4 := by
      simp [next,hflag,hv]
    have hp := call_prefix 2 4 (8*bound.length+10) _ base hr hn
    rw [hfield] at hp
    obtain ⟨tail,ht,hts,htag,hout⟩ := present_tags_tail
      (pre++Streaming.marks (bits.take bound.length)) (bits.drop bound.length)
      (frame (bits.take bound.length)) bound bound.length t cap true
    have he : (pre++Streaming.marks (bits.take bound.length))++frame (bits.drop bound.length)=
        pre++frame bits := by
      rw [List.append_assoc,←Streaming.frame_append,List.take_append_drop]
    have hl : (pre++Streaming.marks (bits.take bound.length)).length=pre.length+2*bound.length := by
      simp [Streaming.marks_length,Nat.min_eq_left hv.1]
    rw [he,hl] at ht hout
    obtain ⟨r,hrun,hfinal,hsteps⟩ := prepend_run hp tail ht
      (show base.steps+1+tail.steps≤8*bound.length+12*t+20 by omega)
    refine ⟨r,hrun,hsteps,?_,?_⟩
    · simpa only [hfinal,presentValid,hv,decide_true,Bool.true_and] using htag
    · intro h
      have ht' : TagScan.tests 4 (TagMachine.valid true) t (bits.drop bound.length)=true := by
        simpa [presentValid,hv] using h
      exact hfinal.trans (hout ht')
  · have hn : next 2 base.final.control base.final.scanned=none := by
      simp [next,hflag,hv]
    have hp := stop_prefix 2 (8*bound.length+10) _ base hr hn
    obtain ⟨r,hrun,hfinal,hsteps⟩ := bounded_run hp
      (show base.steps+1≤8*bound.length+12*t+20 by omega)
      (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
    refine ⟨r,hrun,hsteps,?_,by simp [presentValid,hv]⟩
    have hf : r.final.tapes 7=[false] := by
      simpa only [hfinal,RecoveryCalls.stopped] using hfalse
    simpa [presentValid,hv] using false_result r.final hf

theorem absent_field_tail (pre bits backing bound : List Bool) (j t cap : ℕ) :
    ∃ r, runFrom machine (8*j+12*t+20)
        (cfg (RecoveryCalls.code sizes 3 (programs 3).start)
          (pre++frame bits) backing bound pre.length j t cap false false)=some r ∧
      r.steps≤8*j+12*t+20 ∧ r.final.scanned 7=absentValid bits j t ∧
      (absentValid bits j t=true →
        r.final=cfg (RecoveryCalls.controlCode sizes none)
          (pre++frame bits) backing bound (pre.length+2*j+8*t) j t cap false true) := by
  obtain ⟨base,hr,hs,hfalse,hgood⟩ := zero_checked pre bits backing bound j t cap
  by_cases hv : j≤bits.length ∧ bits.take j=List.replicate j false
  · simp [hv] at hgood
    have hn : next 3 base.final.control base.final.scanned=some 5 := by
      simp [next,hgood,cfg]
    have hp := call_prefix 3 5 (6*j+3) _ base hr hn
    rw [hgood] at hp
    obtain ⟨tail,ht,hts,htag,hout⟩ := absent_tags_tail
      (pre++Streaming.marks (bits.take j)) (bits.drop j) backing bound j t cap false
    have he : (pre++Streaming.marks (bits.take j))++frame (bits.drop j)=pre++frame bits := by
      rw [List.append_assoc,←Streaming.frame_append,List.take_append_drop]
    have hl : (pre++Streaming.marks (bits.take j)).length=pre.length+2*j := by
      simp [Streaming.marks_length,Nat.min_eq_left hv.1]
    rw [he,hl] at ht hout
    obtain ⟨r,hrun,hfinal,hsteps⟩ := prepend_run hp tail ht
      (show base.steps+1+tail.steps≤8*j+12*t+20 by omega)
    refine ⟨r,hrun,hsteps,?_,?_⟩
    · simpa [hfinal,absentValid,hv] using htag
    · intro h
      have ht' : TagScan.tests 4 (TagMachine.valid false) t (bits.drop j)=true := by
        simpa [absentValid,hv] using h
      exact hfinal.trans (hout ht')
  · simp only [hv,↓reduceIte] at hgood
    have hn : next 3 base.final.control base.final.scanned=none := by
      simp [next,hgood]
      exact reject_ne_success
    have hp := stop_prefix 3 (6*j+3) _ base hr hn
    obtain ⟨r,hrun,hfinal,hsteps⟩ := bounded_run hp
      (show base.steps+1≤8*j+12*t+20 by omega)
      (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
    refine ⟨r,hrun,hsteps,?_,by simp [absentValid,hv]⟩
    have hf : r.final.tapes 7=[false] := by
      simpa only [hfinal,RecoveryCalls.stopped] using hfalse
    simpa [absentValid,hv] using false_result r.final hf

end NearCubicWires.RepairSource.VerifierDecoding.RecordMachine
