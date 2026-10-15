import Proof.MachineModel.OrdinaryMatrixCoordinateFields

/-! One actual matrix-coordinate transposition. The payload bit is copied,
the two equal-width coordinate fields are loaded and appended in reverse
order, and only bounded workspace is reset. -/
namespace NearCubicWires.RepairOrdinary.MatrixCoordinateTranspose
open LocalBitMultitape Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def prefixSlots : Fin 2 → Fin 12 := ![7,10]
noncomputable def prefixMachine : Machine 12 3 := RecoveryFocus.machine prefixSlots MatrixCoordinatePrefix.machine
noncomputable def machine : Machine 12 34 := Composition.machine prefixMachine fields

theorem prefix_output (w cap : ℕ) (source record clone rank out : List Bool) (pos : ℕ) (cell : Bool) :
    RecoveryFocus.config prefixSlots (cfg prefixMachine.start w cap source pos record clone rank out).heads
      (cfg prefixMachine.start w cap source pos record clone rank out).tapes
      (MatrixCoordinatePrefix.cfg 2 source (pos+2) (out++[true,cell]))=
      cfg 2 w cap source (pos+2) record clone rank (out++[true,cell]) := by
  have hseven : RecoveryFocus.pick prefixSlots 7=some 0 := RecoveryFocus.pick_slot prefixSlots (by decide) 0
  have hten : RecoveryFocus.pick prefixSlots 10=some 1 := RecoveryFocus.pick_slot prefixSlots (by decide) 1
  apply configuration_ext
  · rfl
  · funext i
    cases hi : RecoveryFocus.pick prefixSlots i with
    | none =>
      have hn7 : i≠7 := by intro he; subst i; rw [hseven] at hi; contradiction
      have hn10 : i≠10 := by intro he; subst i; rw [hten] at hi; contradiction
      have hv7 : i.val≠7 := by intro h; apply hn7; exact Fin.ext h
      have hv10 : i.val≠10 := by intro h; apply hn10; exact Fin.ext h
      simp only [RecoveryFocus.config,hi,cfg,hv7,hv10,↓reduceIte]
    | some j =>
      have hij := RecoveryFocus.slot_of_pick prefixSlots hi
      simp only [RecoveryFocus.config,hi]
      rw [←hij]
      fin_cases j <;> simp [MatrixCoordinatePrefix.cfg,cfg,prefixSlots]
  · funext i
    cases hi : RecoveryFocus.pick prefixSlots i with
    | none =>
      have hn : i≠10 := by intro he; subst i; rw [hten] at hi; contradiction
      simp only [RecoveryFocus.config,hi]
      exact cfg_tapes_out_other prefixMachine.start (2 : Fin 3) w cap source record clone rank out (out++[true,cell]) pos i hn
    | some j =>
      have hij := RecoveryFocus.slot_of_pick prefixSlots hi
      simp only [RecoveryFocus.config,hi]
      rw [←hij]
      fin_cases j <;> simp [MatrixCoordinatePrefix.cfg,cfg,prefixSlots]

theorem prefix_run (w cap : ℕ) (pre suffix record clone rank out : List Bool) (cell : Bool) :
    ∃ actual : ExecutionReceipt 12 3,
      runFrom prefixMachine 2 (cfg prefixMachine.start w cap (pre++[true,cell]++suffix) pre.length record clone rank out)=some actual ∧
      actual.final=cfg 2 w cap (pre++[true,cell]++suffix) (pre.length+2) record clone rank (out++[true,cell]) ∧
      actual.steps=2 := by
  obtain ⟨base,hbase,hf,hs⟩ := MatrixCoordinatePrefix.prefix_run pre suffix out cell
  let source := pre++[true,cell]++suffix
  let entry := cfg prefixMachine.start w cap source pre.length record clone rank out
  let part := MatrixCoordinatePrefix.cfg 0 source pre.length out
  have hi : RecoveryFocus.config prefixSlots entry.heads entry.tapes part=entry := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
  obtain ⟨actual,hr,hfinal,hsteps⟩ := RecoveryFocus.run_config prefixSlots (by decide)
    MatrixCoordinatePrefix.machine entry.heads entry.tapes _ part base hbase
  rw [hi] at hr
  refine ⟨actual,hr,?_,hsteps.trans hs⟩
  rw [hfinal,hf]
  exact prefix_output w cap source record clone rank out pre.length cell

theorem cell_run (w cap : ℕ) (a b pre suffix record clone rank out : List Bool) (cell : Bool)
    (ha : a.length=w) (hb : b.length=w) (hcap : 2*w ≤ cap)
    (hr : record.length ≤ 4*w+1) (hc : clone.length ≤ 4*w+1) (hk : rank.length ≤ 2*w+1) :
    ∃ actual : ExecutionReceipt 12 34,
      runFrom machine (64*w+45) (cfg machine.start w cap (pre++frame (cell::(a++b))++suffix)
        pre.length record clone rank out)=some actual ∧
      actual.final=cfg 33 w cap (pre++frame (cell::(a++b))++suffix) (pre.length+4*w+3)
        (frame (a++b)) (frame (a++b)) (frame b) (out++frame (cell::(b++a))) ∧
      actual.steps ≤ 64*w+45 := by
  obtain ⟨first,hfirst,hff,hfs⟩ := prefix_run w cap pre (frame (a++b)++suffix) record clone rank out cell
  obtain ⟨last,hl,hlf,hls⟩ := fields_run w cap a b (pre++[true,cell]) suffix
    record clone rank (out++[true,cell]) ha hb hcap hr hc hk
  have hsource : pre++[true,cell]++(frame (a++b)++suffix)=pre++frame (cell::(a++b))++suffix := by
    simp [frame,List.append_assoc]
  rw [hsource] at hfirst hff
  have hsource' : (pre++[true,cell])++frame (a++b)++suffix=pre++frame (cell::(a++b))++suffix := by
    simp [frame,List.append_assoc]
  rw [hsource'] at hl hlf
  have hpos : (pre++[true,cell]).length=pre.length+2 := by simp
  rw [hpos] at hl hlf
  have hi : Composition.restart first.final fields.start=
      cfg fields.start w cap (pre++frame (cell::(a++b))++suffix) (pre.length+2)
        record clone rank (out++[true,cell]) := by rw [hff]; rfl
  rw [←hi] at hl
  have hj := Composition.run_join prefixMachine fields 2 (64*w+42)
    (cfg prefixMachine.start w cap (pre++frame (cell::(a++b))++suffix) pre.length record clone rank out)
    first last hfirst hl
  have htime : 2+1+(64*w+42)=64*w+45 := by omega
  rw [htime] at hj
  refine ⟨Composition.joinedReceipt first last,hj,?_,?_⟩
  · change Composition.rightConfig 3 last.final=_
    rw [hlf]
    have hp : pre.length+2+4*w+1=pre.length+4*w+3 := by omega
    have ho : (out++[true,cell])++frame (b++a)=out++frame (cell::(b++a)) := by
      simp [frame,List.append_assoc]
    rw [hp,ho]
    rfl
  · change first.steps+1+last.steps ≤ _
    omega

end NearCubicWires.RepairOrdinary.MatrixCoordinateTranspose
