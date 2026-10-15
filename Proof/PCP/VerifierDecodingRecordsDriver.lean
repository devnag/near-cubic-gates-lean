import Proof.PCP.VerifierDecodingRecordsSemantics

/-! Paid rewind of the capped e-driver, followed by the complete record loop.
The cap backing is retained through the same ordinary execution; zero-padding
transport changes no read, transition, or source cursor. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.RecordsDriver
open LocalBitMultitape RepairOrdinary RecoveryExecution RecordsMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slot : Fin 1 → Fin 9 := fun _ => 8
theorem slot_injective : Function.Injective slot := by intro a b h; exact Subsingleton.elim _ _
theorem slot_pick (i : Fin 9) : RecoveryFocus.pick slot i=if i=8 then some 0 else none := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot slot slot_injective 0
    | simp [RecoveryFocus.pick,slot]

def capacity (c : ℕ) : Fin 9 → ℕ := fun i => if i=8 then c+2 else 0
def cfg {a s : ℕ} (state : Fin a) (base : Configuration 8 s) (c e pos : ℕ) : Configuration 9 a :=
  ⟨state,(fun i => Fin.addCases base.heads (fun _ : Fin 1 => pos) i),
    (fun i => Fin.addCases base.tapes (fun _ : Fin 1 => CapMachine.counter c e) i)⟩
noncomputable def resetProgram := RecoveryFocus.machine slot UnaryTemplate.machine
noncomputable def machine := Composition.machine resetProgram RecordsMachine.machine

theorem padded_cfg (phase : Fin 5) (base : Configuration 8 (Fintype.card (RecoveryCalls.Control RecordMachine.sizes)))
    (c e pos : ℕ) :
    ZeroPadding.config (capacity c) (RepeatMachine.cfg phase base e pos)=
      cfg (RepeatMachine.phaseCode (Fintype.card (RecoveryCalls.Control RecordMachine.sizes)) phase) base c e pos := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i <;>
      simp [ZeroPadding.config,capacity,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
        cfg,CapMachine.counter,CompareMachine.word,Fin.addCases]

theorem focused_cfg {s : ℕ} (base : Configuration 8 s) (c e pos oldPos : ℕ) (q : Fin 3) :
    RecoveryFocus.config slot (cfg 0 base c e oldPos : Configuration 9 3).heads
      (cfg 0 base c e oldPos : Configuration 9 3).tapes
      (UnaryTemplate.config q (CapMachine.counter c e) pos)=cfg q base c e pos := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,slot_pick,cfg,UnaryTemplate.config,Fin.addCases]
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,slot_pick,cfg,UnaryTemplate.config,Fin.addCases]

theorem reset_run {s : ℕ} (base : Configuration 8 s) (c e : ℕ) (he : e≤c) :
    ∃ r, runFrom resetProgram (e+2) (cfg 0 base c e (e+1))=some r ∧
      r.final=cfg 2 base c e 1 ∧ r.steps=e+2 := by
  obtain ⟨baseRun,hr,hf,hs,_⟩ := CapMachine.reset_run c e e he (Nat.le_refl _)
  obtain ⟨r,hrun,hfinal,hsteps⟩ := RecoveryFocus.run_config slot slot_injective UnaryTemplate.machine
    (cfg 0 base c e (e+1) : Configuration 9 3).heads
    (cfg 0 base c e (e+1) : Configuration 9 3).tapes _ _ baseRun hr
  rw [focused_cfg] at hrun
  rw [hf,focused_cfg] at hfinal
  exact ⟨r,hrun,hfinal,hsteps.trans hs⟩

/-- This entry matches the TableBound producer's e-counter at e+1. The
successful guard e≤c is consumed before any record expansion. -/
theorem driver_run (bound : List Bool) (t cap c e : ℕ)
    (hc : 2*bound.length+1≤cap) (he : e≤c) (x : State) (hx : Inv bound x) :
    ∃ r original,
      runFrom machine (e*(8*bound.length+12*t+34)+6)
        (Composition.leftConfig _ (cfg 0 (input bound t cap x) c e (e+1)))=some r ∧
      r.steps≤e*(8*bound.length+12*t+34)+6 ∧
      Checked bound t cap e x original ∧
      r.final=Composition.rightConfig 3 (ZeroPadding.config (capacity c) original) := by
  obtain ⟨first,hfirst,hff,hft⟩ := reset_run (input bound t cap x) c e he
  obtain ⟨base,hbase,hbt,hbf⟩ := checked_run bound t cap e hc x hx
  obtain ⟨tail,htail,htf,htt,_⟩ := ZeroPadding.run_config RecordsMachine.machine (capacity c) _ _ base hbase
  have hi : Composition.restart first.final RecordsMachine.machine.start=
      ZeroPadding.config (capacity c) (RepeatMachine.cfg 0 (input bound t cap x) e 1) := by
    rw [hff,padded_cfg]
    rfl
  rw [←hi] at htail
  have hj := Composition.run_join resetProgram RecordsMachine.machine (e+2)
    (e*(8*bound.length+12*t+33)+3) _ first tail hfirst htail
  have htime : (e+2)+1+(e*(8*bound.length+12*t+33)+3)=e*(8*bound.length+12*t+34)+6 := by ring
  rw [htime] at hj
  refine ⟨Composition.joinedReceipt first tail,base.final,hj,?_,hbf,?_⟩
  · change first.steps+1+tail.steps≤_
    rw [hft,htt]
    nlinarith
  · change Composition.rightConfig 3 tail.final=_
    rw [htf]

end NearCubicWires.RepairSource.VerifierDecoding.RecordsDriver
