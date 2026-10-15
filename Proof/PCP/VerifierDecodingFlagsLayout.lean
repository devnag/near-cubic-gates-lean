import Proof.PCP.VerifierDecodingStartLayout

/-! State-flag scan on the enclosing fourteen-tape store. It consumes the
actual capped state-count counter and advances only the code cursor; all
successful field outputs and arithmetic workspace remain intact. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.FlagsLayout
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev tagStates := Fintype.card TagMachine.Control
abbrev states := Fintype.card (RepeatMachine.Control tagStates)
def slot : Fin 2 → Fin 14 := ![0,2]
theorem slot_injective : Function.Injective slot := by decide
theorem slot_pick (i : Fin 14) : RecoveryFocus.pick slot i=
    if i=0 then some 0 else if i=2 then some 1 else none := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot slot slot_injective 0
    | exact RecoveryFocus.pick_slot slot slot_injective 1
    | simp [RecoveryFocus.pick,slot]
noncomputable def machine := RecoveryFocus.machine slot (TagScan.machine 2 (fun _ => true))
noncomputable def input {a : ℕ} (base : Configuration 14 a) : Configuration 14 states :=
  ⟨machine.start,base.heads,base.tapes⟩
noncomputable def output {a : ℕ} (base : Configuration 14 a) (pre : List Bool) (s : ℕ) :
    Configuration 14 states :=
  ⟨RepeatMachine.phaseCode tagStates 3,
    fun i => if i=0 then pre.length+4*s else base.heads i,base.tapes⟩
structure Entry {a : ℕ} (base : Configuration 14 a) (pre bits : List Bool) (c s : ℕ) : Prop where
  codeHead : base.heads 0=pre.length
  codeTape : base.tapes 0=pre++frame bits
  countHead : base.heads 2=1
  countTape : base.tapes 2=CapMachine.counter c s

theorem focused_input {a : ℕ} (base : Configuration 14 a) (pre bits : List Bool) (c s : ℕ)
    (h : Entry base pre bits c s) :
    RecoveryFocus.config slot base.heads base.tapes
      (ZeroPadding.config ![0,c+2] (TagScan.initial pre bits s))=input base := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,slot_pick,input,ZeroPadding.config,
      TagScan.initial,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,TagMachine.cfg,
      Fin.addCases,h.codeHead,h.countHead]
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,slot_pick,input,ZeroPadding.config,
      TagScan.initial,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,TagMachine.cfg,
      Fin.addCases,h.codeTape,h.countTape,CapMachine.counter,CompareMachine.word]

theorem focused_output {a : ℕ} (base : Configuration 14 a) (pre bits : List Bool) (c s : ℕ)
    (h : Entry base pre bits c s) :
    RecoveryFocus.config slot base.heads base.tapes
      (ZeroPadding.config ![0,c+2] (TagScan.finished pre bits s 2))=output base pre s := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,slot_pick,output,ZeroPadding.config,
      TagScan.finished,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,TagMachine.cfg,
      Fin.addCases,h.countHead]
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,slot_pick,output,ZeroPadding.config,
      TagScan.finished,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,TagMachine.cfg,
      Fin.addCases,h.codeTape,h.countTape,CapMachine.counter,CompareMachine.word]

theorem flags_layout {a : ℕ} (base : Configuration 14 a) (pre bits : List Bool) (c s : ℕ)
    (h : Entry base pre bits c s) :
    ∃ r, runFrom machine (8*s+3) (input base)=some r ∧ r.steps≤8*s+3 ∧
      (if 2*s≤bits.length then r.final=output base pre s
       else r.final.control=RepeatMachine.phaseCode tagStates 4) := by
  obtain ⟨r,hr,hs,hresult⟩ := TagScan.flags_run pre bits s
  obtain ⟨p,hp,hpf,hps,_⟩ := ZeroPadding.run_config (TagScan.machine 2 (fun _ => true))
    ![0,c+2] _ _ r hr
  obtain ⟨f,hfRun,hff,hfs⟩ := RecoveryFocus.run_config slot slot_injective
    (TagScan.machine 2 (fun _ => true)) base.heads base.tapes _ _ p hp
  rw [focused_input base pre bits c s h] at hfRun
  refine ⟨f,hfRun,by omega,?_⟩
  by_cases hlen : 2*s≤bits.length
  · simp only [if_pos hlen] at hresult ⊢
    rw [hff,hpf,hresult,focused_output base pre bits c s h]
  · simp only [if_neg hlen] at hresult ⊢
    simp [hff,hpf,RecoveryFocus.config,ZeroPadding.config,hresult]

end NearCubicWires.RepairSource.VerifierDecoding.FlagsLayout
