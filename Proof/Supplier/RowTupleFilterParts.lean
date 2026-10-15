import Proof.Supplier.RowTupleSubsets
import Proof.Amplification.RecoveryPrefixCompare
import Proof.MachineModel.OrdinaryMatrixFrameCopy

/-! One tuple digit is read at the live source cursor. Reusable comparisons
and an overwriting copy retain the short binary fields between digits. -/
namespace NearCubicWires.RepairOrdinary.RowTupleFilterParts
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Data where
  source : List Bool
  current : ℕ
  bound : ℕ
  previous : ℕ
  boundFlag : Bool
  previousFlag : Bool
  seen : Bool
  good : Bool

def tapes (w : ℕ) (x : Data) : Fin 12→List Bool :=
  ![x.source,frame (binary w x.current),CompareMachine.word w,
    frame (binary w x.bound),[x.boundFlag],List.replicate (4*w+4) false,
    frame (binary w x.previous),[x.previousFlag],[x.seen],[x.good],
    List.replicate (2*w+1) false,List.replicate (4*w+3) false]
def heads (pos : ℕ) : Fin 12→ℕ := ![pos,0,1,0,0,0,0,0,0,0,0,0]
def cfg {s : ℕ} (q : Fin s) (pos w : ℕ) (x : Data) : Configuration 12 s :=
  ⟨q,heads pos,tapes w x⟩
def readMachine := TapeEmbedding.machine 9 FieldMachine.machine

theorem read_run (pre tail : List Bool) (w d : ℕ) (x : Data)
    (hx : x.source=pre++Streaming.marks (binary w d)++tail) :
    ∃ r,runFrom readMachine (4*w+2) (cfg readMachine.start pre.length w x)=some r ∧
      r.final=cfg 4 (pre.length+2*w) w {x with current:=d} ∧ r.steps=4*w+2 := by
  obtain ⟨base,hbase,bf,bs,_⟩ := FieldMachine.field_run pre (binary w d) tail
    (frame (binary w x.current)) (by simp)
  simp only [binary_length] at hbase bf bs
  let extra : Fin 9→List Bool := fun i=>tapes w x (i.natAdd 3)
  let result := TapeEmbedding.receipt (fun _ : Fin 9=>0) extra base
  have hr := TapeEmbedding.run_embed FieldMachine.machine (fun _ : Fin 9=>0) extra _ _ base hbase
  have hi : TapeEmbedding.config (fun _ : Fin 9=>0) extra
      (FieldMachine.scan 0 (pre++Streaming.marks (binary w d)++tail) pre.length w 0 []
        (frame (binary w x.current)))=cfg readMachine.start pre.length w x := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,Fin.addCases,extra,tapes,cfg,
        FieldMachine.scan,StablePartition.Workspace.overlay,hx]
  rw [hi] at hr
  refine ⟨result,hr,?_,bs⟩
  change TapeEmbedding.config _ _ base.final=_
  rw [bf]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> simp [TapeEmbedding.config,Fin.addCases,extra,tapes,cfg,
      FieldMachine.finished,hx]

def compareSlots (prior : Bool) : Fin 4→Fin 12 :=
  if prior then ![1,6,7,5] else ![1,3,4,5]
theorem compare_injective (prior : Bool) : Function.Injective (compareSlots prior) := by
  cases prior <;> decide
def compared (prior : Bool) (x : Data) : Data :=
  if prior then {x with previousFlag:=decide (x.current≤x.previous)}
  else {x with boundFlag:=decide (x.current≤x.bound)}
noncomputable def compareMachine (prior : Bool) :=
  RecoveryFocus.machine (compareSlots prior) RecoveryPrefixCompare.machine

theorem compare_pick (prior : Bool) (i : Fin 12) :
    RecoveryFocus.pick (compareSlots prior) i=
      if i=1 then some 0 else if i=(if prior then 6 else 3) then some 1
      else if i=(if prior then 7 else 4) then some 2 else if i=5 then some 3 else none := by
  have h0 := RecoveryFocus.pick_slot (compareSlots prior) (compare_injective prior) 0
  have h1 := RecoveryFocus.pick_slot (compareSlots prior) (compare_injective prior) 1
  have h2 := RecoveryFocus.pick_slot (compareSlots prior) (compare_injective prior) 2
  have h3 := RecoveryFocus.pick_slot (compareSlots prior) (compare_injective prior) 3
  cases prior <;> fin_cases i
  all_goals first | exact h0 | exact h1 | exact h2 | exact h3 | decide

theorem compare_run (prior : Bool) (pos w : ℕ) (x : Data)
    (hc : x.current<2^w) (hb : x.bound<2^w) (hp : x.previous<2^w) :
    ∃ r,runFrom (compareMachine prior) (4*w+8) (cfg (compareMachine prior).start pos w x)=some r ∧
      r.final.heads=heads pos ∧ r.final.tapes=tapes w (compared prior x) ∧ r.steps=4*w+8 := by
  let right := if prior then x.previous else x.bound
  let flag := if prior then x.previousFlag else x.boundFlag
  have hright : right<2^w := by cases prior <;> assumption
  have ready := RecoveryPrefixCompare.compare_ready (binary w x.current) (binary w right)
    flag (4*w+4) (by simp)
  simp only [binary_length,binary_value _ _ hc,binary_value _ _ hright] at ready
  rw [max_eq_left (by omega : 2*w+3≤4*w+4)] at ready
  obtain ⟨r,hr,rh,rt,rs⟩ := ready.focus_at (compareSlots prior) (compare_injective prior)
    (heads pos) (tapes w x)
    (by intro i; cases prior <;> fin_cases i <;> rfl)
    (by intro i; cases prior <;> fin_cases i <;> rfl)
  refine ⟨r,hr,rh,?_,rs⟩
  rw [rt]
  funext i
  cases prior <;> fin_cases i <;> simp [install,compare_pick,tapes,compared,right]

def updated (x : Data) : Data :=
  {x with seen:=true,good:=x.good && ((!x.seen) || (!x.previousFlag)) && x.boundFlag}
def updateMachine : Machine 12 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q bits=>if q.val=0 then some ⟨1,
    fun i=>if i=8 then some true else if i=9 then some (bits 9 && ((!bits 8) || (!bits 7)) && bits 4)
      else none,fun _=>.stay⟩ else none

theorem update_run (pos w : ℕ) (x : Data) :
    ∃ r,runFrom updateMachine 1 (cfg 0 pos w x)=some r ∧
      r.final=cfg 1 pos w (updated x) ∧ r.steps=1 := by
  have hs : step updateMachine (cfg 0 pos w x)=some (cfg 1 pos w (updated x)) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [cfg,heads,tapes,updated,
        Configuration.scanned,applyAction,writeTapeBit,readTapeBit]
  exact (Timed.single (by rfl) hs).run (by rfl)

def copySlots : Fin 4→Fin 12 := ![1,6,10,11]
theorem copy_injective : Function.Injective copySlots := by decide
noncomputable def copyMachine := RecoveryFocus.machine copySlots MatrixFrameCopy.machine
theorem copy_pick (i : Fin 12) : RecoveryFocus.pick copySlots i=
    if i=1 then some 0 else if i=6 then some 1 else if i=10 then some 2
      else if i=11 then some 3 else none := by
  fin_cases i
  all_goals
    first
    | exact RecoveryFocus.pick_slot copySlots copy_injective 0
    | exact RecoveryFocus.pick_slot copySlots copy_injective 1
    | exact RecoveryFocus.pick_slot copySlots copy_injective 2
    | exact RecoveryFocus.pick_slot copySlots copy_injective 3
    | decide

theorem copy_run (pos w : ℕ) (x : Data) :
    ∃ r,runFrom copyMachine (8*w+8) (cfg copyMachine.start pos w x)=some r ∧
      r.final.heads=heads pos ∧ r.final.tapes=tapes w {x with previous:=x.current} ∧ r.steps=8*w+8 := by
  obtain ⟨base,hr,ht,hh,hs⟩ := MatrixFrameCopy.copy_run (binary w x.current)
    (frame (binary w x.previous)) (by simp)
  simp only [binary_length] at hr ht hs
  have ready : ReadyRun MatrixFrameCopy.machine (8*w+8)
      ![frame (binary w x.current),frame (binary w x.previous),List.replicate (2*w+1) false,
        List.replicate (4*w+3) false]
      ![frame (binary w x.current),frame (binary w x.current),List.replicate (2*w+1) false,
        List.replicate (4*w+3) false] := by
    refine ⟨base,?_,ht,hh,hs⟩
    simpa only [MatrixFrameCopy.input,binary_length] using hr
  obtain ⟨r,hr,rh,rt,rs⟩ := ready.focus_at copySlots copy_injective (heads pos) (tapes w x)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  refine ⟨r,hr,rh,?_,rs⟩
  rw [rt]
  funext i
  fin_cases i <;> simp [install,copy_pick,tapes]

end NearCubicWires.RepairOrdinary.RowTupleFilterParts
