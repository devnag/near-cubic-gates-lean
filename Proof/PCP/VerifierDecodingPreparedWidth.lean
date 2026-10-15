import Proof.PCP.VerifierDecodingCounterReset

/-! Execute the binary-state/width producer on the guarded header's actual
capped state counter. The code cursor, tape count, length guard and result
remain untouched; five new work tapes start blank. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.PreparedWidth
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slot : Fin 6 → Fin 11 := ![2,6,7,8,9,10]
theorem slot_injective : Function.Injective slot := by decide
theorem slot_pick (i : Fin 11) :
    RecoveryFocus.pick slot i=![none,none,some 0,none,none,none,some 1,some 2,some 3,some 4,some 5] i := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot slot slot_injective 0
    | exact RecoveryFocus.pick_slot slot slot_injective 1
    | exact RecoveryFocus.pick_slot slot slot_injective 2
    | exact RecoveryFocus.pick_slot slot slot_injective 3
    | exact RecoveryFocus.pick_slot slot slot_injective 4
    | exact RecoveryFocus.pick_slot slot slot_injective 5
    | simp [RecoveryFocus.pick,slot]
  all_goals intro j; fin_cases j <;> decide

noncomputable def machine := RecoveryFocus.machine slot BitWidthMachine.machine
def capacity (c : ℕ) : Fin 6 → ℕ := ![c+2,0,0,0,0,0]
noncomputable def input {a : ℕ} (base : Configuration 6 a) : Configuration 11 25 :=
  ⟨machine.start,
    fun i => Fin.addCases base.heads (fun _ : Fin 5 => 0) i,
    fun i => Fin.addCases base.tapes (fun _ : Fin 5 => []) i⟩
def output {a : ℕ} (base : Configuration 6 a) (s x y : ℕ) : Configuration 11 25 :=
  ⟨(BitWidthMachine.output s x y).control,
    fun i => Fin.addCases base.heads ![0,0,0,0,1] i,
    fun i => Fin.addCases base.tapes
      ![BitWidthMachine.framed s,BitWidthMachine.dimension s,List.replicate x false,
        List.replicate y false,CompareMachine.word (BitWidthMachine.width s)] i⟩

theorem focused_input {a : ℕ} (base : Configuration 6 a) (c s : ℕ)
    (hh : base.heads 2=1) (ht : base.tapes 2=CapMachine.counter c s) :
    RecoveryFocus.config slot (input base).heads (input base).tapes
      (ZeroPadding.config (capacity c) (BitWidthMachine.input s))=input base := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,slot_pick,input,ZeroPadding.config,
      BitWidthMachine.input,Composition.leftConfig,BitWidthMachine.frameInput,
      Fin.addCases,hh]
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,slot_pick,input,ZeroPadding.config,
      capacity,BitWidthMachine.input,Composition.leftConfig,BitWidthMachine.frameInput,
      Fin.addCases,ht,CapMachine.counter,CompareMachine.word]

theorem focused_output {a : ℕ} (base : Configuration 6 a) (c s x y : ℕ)
    (hh : base.heads 2=1) (ht : base.tapes 2=CapMachine.counter c s) :
    RecoveryFocus.config slot (input base).heads (input base).tapes
      (ZeroPadding.config (capacity c) (BitWidthMachine.output s x y))=output base s x y := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,slot_pick,input,output,ZeroPadding.config,
      BitWidthMachine.output,Composition.rightConfig,BitWidthMachine.finished,Fin.addCases,hh]
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,slot_pick,input,output,ZeroPadding.config,
      capacity,BitWidthMachine.output,Composition.rightConfig,BitWidthMachine.finished,
      Fin.addCases,ht,CapMachine.counter,CompareMachine.word]

theorem width_run {a : ℕ} (base : Configuration 6 a) (c s : ℕ)
    (hh : base.heads 2=1) (ht : base.tapes 2=CapMachine.counter c s)
    (hs : 0<s) (hc : s≤c) :
    ∃ x y, x≤2*PCPResourceLedger.ell s+3 ∧
      y≤ClockInputLength.cost s (List.replicate s true) ∧
      ∃ r, runFrom machine (8*c^2+34*c+11) (input base)=some r ∧
        r.final=output base s x y ∧ r.steps≤8*c^2+34*c+11 := by
  obtain ⟨x,y,hx,hy,r,hr,hf,htime⟩ := BitWidthMachine.bit_width_run s hs
  obtain ⟨p,hp,hpf,hps,_⟩ := ZeroPadding.run_config BitWidthMachine.machine (capacity c) _ _ r hr
  obtain ⟨f,hfRun,hff,hfs⟩ := RecoveryFocus.run_config slot slot_injective
    BitWidthMachine.machine (input base).heads (input base).tapes _ _ p hp
  rw [focused_input base c s hh ht] at hfRun
  rw [hpf,hf,focused_output base c s x y hh ht] at hff
  have hbudget := BitWidthMachine.budget_bound c s hc
  have hm := runFrom_moreFuel machine (BitWidthMachine.budget s)
    (8*c^2+34*c+11-BitWidthMachine.budget s) _ f hfRun
  rw [Nat.add_sub_of_le hbudget] at hm
  exact ⟨x,y,hx,hy,f,hm,hff,by omega⟩

theorem output_binary {a : ℕ} (base : Configuration 6 a) (s x y : ℕ) (hs : 0<s) :
    (output base s x y).tapes 7=frame (VerifierEncoding.fixedBits (natBitLength s) s) ∧
    (output base s x y).tapes 10=CompareMachine.word (natBitLength s) := by
  have he : VerifierEncoding.fixedBits (natBitLength s) s=ClockBinary.word s := by
    rw [fixedBits_binary,←BitWidthMachine.width_eq s hs]
    exact ClockBinary.word_binary s
  simp [output,BitWidthMachine.dimension,BitWidthMachine.width_eq s hs,he,Fin.addCases]

end NearCubicWires.RepairSource.VerifierDecoding.PreparedWidth
