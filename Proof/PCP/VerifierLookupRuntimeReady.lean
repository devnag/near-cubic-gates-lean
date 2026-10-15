import Proof.PCP.VerifierLookupRuntimeStore

/-! Reusable entry calls on the fixed lookup store. Inactive source heads
are retained while local query builders execute and reset their own heads. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ready_lift {t s time : ℕ} (slot : Fin t→Fin 21) (hi : Function.Injective slot)
    (p : Machine t s) (input output : Fin t→List Bool) (d e : Store)
    (h : ReadyRun p time input output)
    (hin : ∀ i,(cfg p.start d).tapes (slot i)=input i)
    (hh : ∀ i,(cfg p.start d).heads (slot i)=0)
    (hout : ∀ i,(cfg p.start e).tapes (slot i)=output i)
    (he : ∀ i,(cfg p.start e).heads (slot i)=0)
    (oh : ∀ i,(∀ j,slot j≠i) → (cfg p.start d).heads i=(cfg p.start e).heads i)
    (ot : ∀ i,(∀ j,slot j≠i) → (cfg p.start d).tapes i=(cfg p.start e).tapes i) :
    ∃ r,runFrom (RecoveryFocus.machine slot p) time (cfg p.start d)=some r ∧
      r.final=cfg r.final.control e ∧ r.steps=time := by
  obtain ⟨base,hb,hbt,hbh,hbs⟩ := h
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config slot hi p (cfg p.start d).heads (cfg p.start d).tapes _ _ base hb
  have hinput : RecoveryFocus.config slot (cfg p.start d).heads (cfg p.start d).tapes
      (initialConfiguration p input)=cfg p.start d := by
    apply TransitionEvent.focused_eq slot hi (cfg p.start d)
    · rfl
    · intro i; exact (hh i).symm
    · intro i; exact (hin i).symm
    · intro i _; rfl
    · intro i _; rfl
  rw [hinput] at hr
  have houtput : RecoveryFocus.config slot (cfg p.start d).heads (cfg p.start d).tapes base.final=
      cfg base.final.control e := by
    apply TransitionEvent.focused_eq slot hi (cfg p.start d)
    · rfl
    · intro i; exact (hbh i).trans (he i).symm
    · intro i; rw [hbt]; exact (hout i).symm
    · exact oh
    · exact ot
  exact ⟨r,hr,by rw [hrf,houtput]; rfl,hrs.trans hbs⟩

theorem clear_run (d : Store) :
    ∃ r,runFrom clearProgram 1 (cfg clearProgram.start d)=some r ∧
      r.final=cfg r.final.control (cleared d) ∧ r.steps=1 := by
  apply ready_lift clearSlots (by decide) LookupReadBit.clear (fun _=>[d.flag]) (fun _=>[false]) d (cleared d)
    (LookupReadBit.clear_ready d.flag)
  · intro i; fin_cases i; rfl
  · intro i; fin_cases i; rfl
  · intro i; fin_cases i; rfl
  · intro i; fin_cases i; rfl
  · intro i _; rfl
  · intro i h; fin_cases i <;> first | exact False.elim (h 0 rfl) | rfl

theorem flags_query_run (d : Store) (hf : d.flag=false)
    (hb : d.flagQuery.length≤2*d.state.length+1)
    (hz : d.flagCounter.length≤2*d.state.length+1) (hc : 2*d.state.length+2≤d.cap) :
    ∃ r,runFrom flagsQueryProgram (4*d.state.length+6) (cfg flagsQueryProgram.start d)=some r ∧
      r.final=cfg r.final.control (flagsInitialized d) ∧ r.steps=4*d.state.length+6 := by
  have h := LookupQuery.query_ready [] d.state d.flagQuery d.flagCounter d.cap
    (by simpa only [List.length_nil,Nat.zero_add] using hb)
    (by simpa only [List.length_nil,Nat.zero_add] using hz)
    (by simpa only [List.length_nil,Nat.zero_add] using hc)
  simp only [List.length_nil,Nat.zero_add,List.nil_append] at h
  apply ready_lift flagsQuerySlots (by decide) LookupQuery.machine _ _ d (flagsInitialized d) h
  · intro i; fin_cases i <;> first | rfl | (change [d.flag]=frame []; rw [hf]; rfl)
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> first | rfl | (change [d.flag]=frame []; rw [hf]; rfl)
  · intro i; fin_cases i <;> rfl
  · intro i _; rfl
  · intro i h; fin_cases i <;> first | exact False.elim (h 2 rfl) | exact False.elim (h 3 rfl) | rfl

theorem table_query_run (d : Store) (bits : List Bool) (hs : d.scanCopy=frame bits)
    (hb : d.query.length≤2*(bits.length+d.state.length)+1)
    (hz : d.counter.length≤2*(bits.length+d.state.length)+1)
    (hc : 2*(bits.length+d.state.length)+2≤d.cap) :
    ∃ r,runFrom tableQueryProgram (4*(bits.length+d.state.length)+6) (cfg tableQueryProgram.start d)=some r ∧
      r.final=cfg r.final.control (tableInitialized d bits) ∧ r.steps=4*(bits.length+d.state.length)+6 := by
  have h := LookupQuery.query_ready bits d.state d.query d.counter d.cap hb hz hc
  apply ready_lift tableQuerySlots (by decide) LookupQuery.machine _ _ d (tableInitialized d bits) h
  · intro i; fin_cases i <;> first | rfl | exact hs
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> first | rfl | exact hs
  · intro i; fin_cases i <;> rfl
  · intro i _; rfl
  · intro i h; fin_cases i <;> first | exact False.elim (h 2 rfl) | exact False.elim (h 3 rfl) | rfl

end NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
