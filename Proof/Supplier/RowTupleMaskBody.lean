import Proof.Supplier.RowMaskLookupReusable
import Proof.Supplier.RowTupleDerivedEnumeration

/-! Each tuple digit is read into the actual mask-lookup bound tape. The
lookup then appends that cached monomial's occurrence positions and updates
the physical count, retaining repeated occurrences across selected rows. -/
namespace NearCubicWires.RepairOrdinary.RowTupleMaskBody
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding RowMaskPositionParts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def readSlots : Fin 3→Fin 12 := ![10,6,11]
def lookupSlots (i : Fin 10) : Fin 12 := i.castAdd 2
theorem read_injective : Function.Injective readSlots := by decide
theorem lookup_injective : Function.Injective lookupSlots := by
  intro i j h; exact Fin.ext (congrArg (fun a : Fin 12=>a.val) h)
noncomputable def read := RecoveryFocus.machine readSlots FieldMachine.machine
noncomputable def lookup := TapeEmbedding.machine 2 RowMaskLookupReusable.machine
noncomputable def machine := Composition.machine read lookup
def cfg {s : ℕ} (q : Fin s) (N w M : ℕ) (tuple : List Bool) (pos : ℕ) (x : Data) : Configuration 12 s :=
  ⟨q,Fin.addCases (m:=10) (n:=2) (motive:=fun _=>ℕ)
    (RowMaskLookupReusable.cfg q N w M x).heads ![pos,1],
    Fin.addCases (m:=10) (n:=2) (motive:=fun _=>List Bool)
    (RowMaskLookupReusable.cfg q N w M x).tapes ![tuple,CompareMachine.word w]⟩
def budget (N w M : ℕ) := 2*RowMaskLookupReusable.capacity N w M+4*w+5

theorem read_pick (i : Fin 12) : RecoveryFocus.pick readSlots i=
    if i=10 then some 0 else if i=6 then some 1 else if i=11 then some 2 else none := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot readSlots read_injective 0
    | exact RecoveryFocus.pick_slot readSlots read_injective 1
    | exact RecoveryFocus.pick_slot readSlots read_injective 2
    | decide

theorem read_run (N w M d : ℕ) (tuple pre tail : List Bool) (x : Data)
    (ht : tuple=pre++Streaming.marks (binary w d)++tail) :
    ∃ r,runFrom read (4*w+2) (cfg read.start N w M tuple pre.length x)=some r ∧
      r.final.heads=(cfg read.start N w M tuple (pre.length+2*w) {x with bound:=d}).heads ∧
      r.final.tapes=(cfg read.start N w M tuple (pre.length+2*w) {x with bound:=d}).tapes ∧
      r.steps=4*w+2 := by
  obtain ⟨base,hbase,bf,bs,_⟩ := FieldMachine.field_run pre (binary w d) tail
    (frame (binary w x.bound)) (by simp)
  simp only [binary_length] at hbase bs
  let ambient := cfg read.start N w M tuple pre.length x
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config readSlots read_injective FieldMachine.machine
    ambient.heads ambient.tapes _ _ base hbase
  have hi : RecoveryFocus.config readSlots ambient.heads ambient.tapes
      (FieldMachine.scan 0 (pre++Streaming.marks (binary w d)++tail) pre.length w 0 []
        (frame (binary w x.bound)))=ambient := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i
      · exact ht
      · simp [ambient,cfg,readSlots,RowMaskLookupReusable.cfg,RowMaskConsume.bank,ZeroPadding.config,
          RowMaskPositionParts.cfg,RowMaskPositionParts.tapes,RowMaskConsume.capacities,ZeroPadding.pad,
          FieldMachine.scan,StablePartition.Workspace.overlay,Fin.addCases]
      · rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,rs.trans bs⟩
  · rw [rf,bf]
    funext i; fin_cases i <;> simp [RecoveryFocus.config,read_pick,FieldMachine.finished,ambient,cfg,
      RowMaskLookupReusable.cfg,RowMaskPositionParts.heads,Fin.addCases]
  · rw [rf,bf]
    funext i; fin_cases i <;> simp [RecoveryFocus.config,read_pick,FieldMachine.finished,ambient,cfg,
      RowMaskLookupReusable.cfg,RowMaskConsume.bank,ZeroPadding.config,RowMaskPositionParts.cfg,
      RowMaskPositionParts.tapes,RowMaskConsume.capacities,ZeroPadding.pad,Fin.addCases,ht]

theorem body_run (N w M : ℕ) (rows : List (List Bool)) (bits cacheTail tuple pre tail : List Bool)
    (x : Data) (ht : tuple=pre++Streaming.marks (binary w rows.length)++tail)
    (hx : x.source=rows.flatten++bits++cacheTail) (hp : x.pos=0) (hi : x.index=0)
    (hl : ∀ row∈rows,row.length=N) (hn : bits.length=N) (hc : x.counter=0)
    (hb : rows.length+1<2^w) (hM : rows.length≤M) :
    ∃ r,runFrom machine (budget N w M) (cfg machine.start N w M tuple pre.length x)=some r ∧
      r.final.heads=(cfg machine.start N w M tuple (pre.length+2*w)
        (RowMaskLookupReusable.result bits {x with bound:=rows.length})).heads ∧
      r.final.tapes=(cfg machine.start N w M tuple (pre.length+2*w)
        (RowMaskLookupReusable.result bits {x with bound:=rows.length})).tapes ∧
      r.steps≤budget N w M := by
  obtain ⟨a,ha,ah,atapes,_⟩ := read_run N w M rows.length tuple pre tail x ht
  let y := {x with bound:=rows.length}
  obtain ⟨base,hbase,bh,bt,_⟩ := RowMaskLookupReusable.lookup_run N w M rows bits cacheTail y
    hx hp hi hl hn hc rfl hb hM
  let b := TapeEmbedding.receipt ![pre.length+2*w,1] ![tuple,CompareMachine.word w] base
  have hbRun := TapeEmbedding.run_embed RowMaskLookupReusable.machine
    ![pre.length+2*w,1] ![tuple,CompareMachine.word w] _ _ base hbase
  have hinit : TapeEmbedding.config ![pre.length+2*w,1] ![tuple,CompareMachine.word w]
      (RowMaskLookupReusable.cfg RowMaskLookupReusable.machine.start N w M y)=
      Composition.restart a.final lookup.start := by
    apply configuration_ext
    · rfl
    · change _=a.final.heads
      rw [ah]
      rfl
    · change _=a.final.tapes
      rw [atapes]
      rfl
  rw [hinit] at hbRun
  have hwhole := Composition.run_join read lookup _ _ _ a b ha hbRun
  have htBudget : 4*w+2+1+(2*RowMaskLookupReusable.capacity N w M+2)=budget N w M := by unfold budget; omega
  rw [htBudget] at hwhole
  refine ⟨Composition.joinedReceipt a b,hwhole,?_,?_,runFrom_steps_le machine _ _ _ hwhole⟩
  · change b.final.heads=_
    change Fin.addCases (m:=10) (n:=2) (motive:=fun _ : Fin 12=>ℕ) base.final.heads ![pre.length+2*w,1]=_
    rw [bh]
    rfl
  · change b.final.tapes=_
    change Fin.addCases (m:=10) (n:=2) (motive:=fun _ : Fin 12=>List Bool) base.final.tapes ![tuple,CompareMachine.word w]=_
    rw [bt]
    rfl

end NearCubicWires.RepairOrdinary.RowTupleMaskBody
