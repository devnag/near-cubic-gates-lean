import Proof.PCP.VerifierLookupRuntimeReady

/-! Both paid code navigation entries are wired into the same lookup store.
The claimed-witness cursor and every output/event-external tape are retained. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem navigation_place {n : ℕ} (q : Fin n) (d : Store) (pos : ℕ) :
    RecoveryFocus.config navigationSlots (cfg q d).heads (cfg q d).tapes
      (LookupNavigation.cfg q (LookupNavigation.positioned (navigation d) pos))=
      cfg q (positioned d pos) := by
  apply TransitionEvent.focused_eq navigationSlots (by decide) (cfg q d)
  · rfl
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i h; fin_cases i <;> first | exact False.elim (h 0 rfl) | rfl
  · intro i _; rfl

theorem navigation_lift (table : Bool) (d : Store) (pos fuel : ℕ)
    (base : ExecutionReceipt 5 (Fintype.card (RecoveryCalls.Control LookupNavigation.sizes)))
    (hb : runFrom (LookupNavigation.machine table) fuel
      (LookupNavigation.cfg (LookupNavigation.machine table).start (navigation d))=some base)
    (hbf : base.final=LookupNavigation.cfg base.final.control
      (LookupNavigation.positioned (navigation d) pos)) :
    ∃ r,runFrom (RecoveryFocus.machine navigationSlots (LookupNavigation.machine table)) fuel
      (cfg (LookupNavigation.machine table).start d)=some r ∧
      r.final=cfg r.final.control (positioned d pos) ∧ r.steps≤fuel := by
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config navigationSlots (by decide) (LookupNavigation.machine table)
    (cfg (LookupNavigation.machine table).start d).heads (cfg (LookupNavigation.machine table).start d).tapes _ _ base hb
  have hi := navigation_place (LookupNavigation.machine table).start d d.codePos
  have hi' : RecoveryFocus.config navigationSlots (cfg (LookupNavigation.machine table).start d).heads
      (cfg (LookupNavigation.machine table).start d).tapes
      (LookupNavigation.cfg (LookupNavigation.machine table).start (navigation d))=
      cfg (LookupNavigation.machine table).start d := hi
  rw [hi'] at hr
  have ho : RecoveryFocus.config navigationSlots (cfg (LookupNavigation.machine table).start d).heads
      (cfg (LookupNavigation.machine table).start d).tapes base.final=cfg base.final.control (positioned d pos) := by
    rw [hbf]
    exact navigation_place _ d pos
  have hs := runFrom_steps_le (LookupNavigation.machine table) fuel _ base hb
  exact ⟨r,hr,by rw [hrf,ho]; rfl,hrs.trans_le hs⟩

theorem flags_navigation_run (d : Store) (hp : d.codePos≤2*d.code.length+1) :
    ∃ r,runFrom flagsNavigationProgram (3*d.code.length+3*d.t+3*d.s+3*d.j+20)
      (cfg flagsNavigationProgram.start d)=some r ∧
      r.final=cfg r.final.control (positioned d (2*(d.t+d.s+d.j+2))) ∧
      r.steps≤3*d.code.length+3*d.t+3*d.s+3*d.j+20 := by
  obtain ⟨base,hb,hbf,_⟩ := LookupNavigation.flags_run (navigation d) hp
  exact navigation_lift false d _ _ base hb (by rw [hbf]; rfl)

theorem table_navigation_run (d : Store) (hp : d.codePos≤2*d.code.length+1) :
    ∃ r,runFrom tableNavigationProgram (3*d.code.length+3*d.t+9*d.s+3*d.j+26)
      (cfg tableNavigationProgram.start d)=some r ∧
      r.final=cfg r.final.control (positioned d (2*(d.t+3*d.s+d.j+2))) ∧
      r.steps≤3*d.code.length+3*d.t+9*d.s+3*d.j+26 := by
  obtain ⟨base,hb,hbf,_⟩ := LookupNavigation.table_run (navigation d) hp
  exact navigation_lift true d _ _ base hb (by rw [hbf]; rfl)

end NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
