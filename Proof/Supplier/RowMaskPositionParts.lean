import Proof.Supplier.RowBinaryClear
import Proof.MachineModel.OrdinaryMatrixRawBlock

/-! Retained packed-mask positioning uses a short binary row counter and
one physical raw-row skip. The native occurrence output remains live. -/
namespace NearCubicWires.RepairOrdinary.RowMaskPositionParts
open LocalBitMultitape RecoveryExecution RecoveryRootRound Streaming SignedSortKey RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Data where
  source : List Bool
  pos : ℕ
  index : ℕ
  count : ℕ
  out : List Bool
  counter : ℕ
  bound : ℕ
  flag : Bool

def heads (x : Data) : Fin 9→ℕ := ![x.pos,1,x.out.length,x.count+1,1,0,0,0,0]
def tapes (N w : ℕ) (x : Data) : Fin 9→List Bool :=
  ![x.source,UnaryTemplate.tape x.index,x.out,CompareMachine.word x.count,UnaryTemplate.tape N,
    frame (binary w x.counter),frame (binary w x.bound),[x.flag],List.replicate (2*w+1) false]
def cfg {s : ℕ} (q : Fin s) (N w : ℕ) (x : Data) : Configuration 9 s := ⟨q,heads x,tapes N w x⟩
def advanced (x : Data) : Data :=
  {x with counter:=x.counter+1,flag:=decide (x.counter+1≤x.bound)}
def counterSlots : Fin 4→Fin 9 := ![5,6,7,8]
theorem counter_injective : Function.Injective counterSlots := by decide
noncomputable def counterMachine := RecoveryFocus.machine counterSlots RowTupleCounter.machine

theorem counter_pick (i : Fin 9) : RecoveryFocus.pick counterSlots i=
    if i=5 then some 0 else if i=6 then some 1 else if i=7 then some 2 else if i=8 then some 3 else none := by
  fin_cases i
  all_goals
    first
    | exact RecoveryFocus.pick_slot counterSlots counter_injective 0
    | exact RecoveryFocus.pick_slot counterSlots counter_injective 1
    | exact RecoveryFocus.pick_slot counterSlots counter_injective 2
    | exact RecoveryFocus.pick_slot counterSlots counter_injective 3
    | decide

theorem counter_run (N w : ℕ) (x : Data)
    (hc : x.counter+1<2^w) (hb : x.bound<2^w) :
    ∃ r,runFrom counterMachine (8*w+9) (cfg counterMachine.start N w x)=some r ∧
      r.final=cfg 13 N w (advanced x) := by
  obtain ⟨base,hbase,bf⟩ := RowTupleCounter.next_run w x.counter x.bound (2*w+1) x.flag hc hb (by omega)
  let ambient := cfg counterMachine.start N w x
  obtain ⟨r,hr,rf,_⟩ := RecoveryFocus.run_config counterSlots counter_injective RowTupleCounter.machine
    ambient.heads ambient.tapes _ _ base hbase
  have hi : RecoveryFocus.config counterSlots ambient.heads ambient.tapes
      (WitnessCounterCheck.config RowTupleCounter.machine.start w x.counter x.bound (2*w+1) x.flag)=ambient := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
  rw [hi] at hr
  refine ⟨r,hr,?_⟩
  rw [rf,bf]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,counter_pick,ambient,cfg,heads,WitnessCounterCheck.config,advanced]
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,counter_pick,ambient,cfg,tapes,WitnessCounterCheck.config,advanced]

def skipSlots : Fin 3→Fin 9 := ![4,0,2]
theorem skip_injective : Function.Injective skipSlots := by decide
noncomputable def skipMachine := RecoveryFocus.machine skipSlots (MatrixRawBlock.machine false)
theorem skip_pick (i : Fin 9) : RecoveryFocus.pick skipSlots i=
    if i=4 then some 0 else if i=0 then some 1 else if i=2 then some 2 else none := by
  fin_cases i
  all_goals
    first
    | exact RecoveryFocus.pick_slot skipSlots skip_injective 0
    | exact RecoveryFocus.pick_slot skipSlots skip_injective 1
    | exact RecoveryFocus.pick_slot skipSlots skip_injective 2
    | decide

theorem skip_run (N w : ℕ) (x : Data) (pre bits suffix : List Bool)
    (hx : x.source=pre++bits++suffix) (hp : x.pos=pre.length) (hn : bits.length=N) :
    ∃ r,runFrom skipMachine (2*N+4) (cfg skipMachine.start N w x)=some r ∧
      r.final=cfg 4 N w {x with pos:=x.pos+N} ∧ r.steps=2*N+4 := by
  obtain ⟨base,hbase,bf,bs,_⟩ := MatrixRawBlock.block_run false pre bits suffix x.out
  rw [hn] at hbase bs
  let ambient := cfg skipMachine.start N w x
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config skipSlots skip_injective (MatrixRawBlock.machine false)
    ambient.heads ambient.tapes _ _ base hbase
  have hi : RecoveryFocus.config skipSlots ambient.heads ambient.tapes
      (MatrixRawBlock.config 0 (UnaryTemplate.tape N) 1 (pre++bits++suffix) pre.length x.out)=ambient := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i
      · rfl
      · exact hp
      · rfl
    · intro i; fin_cases i
      · rfl
      · exact hx
      · rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,rs.trans bs⟩
  rw [rf,bf]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,skip_pick,ambient,cfg,heads,MatrixRawBlock.config,MatrixRawBlock.selected,hp,hn]
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,skip_pick,ambient,cfg,tapes,MatrixRawBlock.config,MatrixRawBlock.selected,hx,hn]

end NearCubicWires.RepairOrdinary.RowMaskPositionParts
