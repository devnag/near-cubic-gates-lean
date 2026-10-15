import Proof.PCP.VerifierDecodingRecordCalls

/-! The two action-tag exits of the actual record validator, including the
paid success-bit write. Invalid or truncated tags halt with a false bit. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.RecordMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem reject_ne_success :
    RepeatMachine.phaseCode (Fintype.card TagMachine.Control) 4 ≠
      RepeatMachine.phaseCode (Fintype.card TagMachine.Control) 3 := by
  intro h
  have he := (RepeatMachine.code (Fintype.card TagMachine.Control)).injective h
  exact (by decide : (4 : Fin 5) ≠ 3) (Sum.inr.inj he)

theorem present_tags_tail (pre bits backing bound : List Bool) (j t cap : ℕ) (rangeFlag : Bool) :
    ∃ r, runFrom machine (12*t+6)
        (cfg (RecoveryCalls.code sizes 4 (programs 4).start)
          (pre++frame bits) backing bound pre.length j t cap rangeFlag false)=some r ∧
      r.steps≤12*t+6 ∧ r.final.scanned 7=TagScan.tests 4 (TagMachine.valid true) t bits ∧
      (TagScan.tests 4 (TagMachine.valid true) t bits=true →
        r.final=cfg (RecoveryCalls.controlCode sizes none)
          (pre++frame bits) backing bound (pre.length+8*t) j t cap rangeFlag true) := by
  obtain ⟨base,hr,hs,hfalse,hcheck⟩ := tags_checked pre bits backing bound j t cap true rangeFlag
  cases ht : TagScan.tests 4 (TagMachine.valid true) t bits with
  | false =>
    simp only [ht,Bool.false_eq_true,↓reduceIte] at hcheck
    have hn : next 4 base.final.control base.final.scanned=none := by
      simp [next,hcheck]
      exact reject_ne_success
    have hp := stop_prefix 4 (12*t+3) _ base hr hn
    obtain ⟨r,hrun,hfinal,hsteps⟩ := bounded_run hp (show base.steps+1≤12*t+6 by omega)
      (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
    refine ⟨r,hrun,hsteps,?_,by simp⟩
    apply false_result
    simpa only [hfinal,RecoveryCalls.stopped] using hfalse
  | true =>
    simp only [ht,↓reduceIte] at hcheck
    have hn : next 4 base.final.control base.final.scanned=some 6 := by
      simp [next,hcheck,cfg]
    have hp := call_prefix 4 6 (12*t+3) _ base hr hn
    rw [hcheck] at hp
    have hlast := success_tail (pre++frame bits) backing bound (pre.length+8*t) j t cap rangeFlag
    have hall := hp.trans hlast
    obtain ⟨r,hrun,hfinal,hsteps⟩ := bounded_run hall (show base.steps+1+2≤12*t+6 by omega)
      (by simp [machine,RecoveryCalls.machine,cfg])
    refine ⟨r,hrun,hsteps,?_,fun _ => hfinal⟩
    simp [hfinal,cfg,Configuration.scanned,readTapeBit,List.getD]

theorem absent_tags_tail (pre bits backing bound : List Bool) (j t cap : ℕ) (rangeFlag : Bool) :
    ∃ r, runFrom machine (12*t+6)
        (cfg (RecoveryCalls.code sizes 5 (programs 5).start)
          (pre++frame bits) backing bound pre.length j t cap rangeFlag false)=some r ∧
      r.steps≤12*t+6 ∧ r.final.scanned 7=TagScan.tests 4 (TagMachine.valid false) t bits ∧
      (TagScan.tests 4 (TagMachine.valid false) t bits=true →
        r.final=cfg (RecoveryCalls.controlCode sizes none)
          (pre++frame bits) backing bound (pre.length+8*t) j t cap rangeFlag true) := by
  obtain ⟨base,hr,hs,hfalse,hcheck⟩ := tags_checked pre bits backing bound j t cap false rangeFlag
  cases ht : TagScan.tests 4 (TagMachine.valid false) t bits with
  | false =>
    simp only [ht,Bool.false_eq_true,↓reduceIte] at hcheck
    have hn : next 5 base.final.control base.final.scanned=none := by
      simp [next,hcheck]
      exact reject_ne_success
    have hp := stop_prefix 5 (12*t+3) _ base hr hn
    obtain ⟨r,hrun,hfinal,hsteps⟩ := bounded_run hp (show base.steps+1≤12*t+6 by omega)
      (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
    refine ⟨r,hrun,hsteps,?_,by simp⟩
    apply false_result
    simpa only [hfinal,RecoveryCalls.stopped] using hfalse
  | true =>
    simp only [ht,↓reduceIte] at hcheck
    have hn : next 5 base.final.control base.final.scanned=some 6 := by
      simp [next,hcheck,cfg]
    have hp := call_prefix 5 6 (12*t+3) _ base hr hn
    rw [hcheck] at hp
    have hlast := success_tail (pre++frame bits) backing bound (pre.length+8*t) j t cap rangeFlag
    have hall := hp.trans hlast
    obtain ⟨r,hrun,hfinal,hsteps⟩ := bounded_run hall (show base.steps+1+2≤12*t+6 by omega)
      (by simp [machine,RecoveryCalls.machine,cfg])
    refine ⟨r,hrun,hsteps,?_,fun _ => hfinal⟩
    simp [hfinal,cfg,Configuration.scanned,readTapeBit,List.getD]

end NearCubicWires.RepairSource.VerifierDecoding.RecordMachine
