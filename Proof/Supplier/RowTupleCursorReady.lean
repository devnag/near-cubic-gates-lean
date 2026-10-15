import Proof.Supplier.RowTupleMaskLoop
import Proof.Supplier.RowMaskLookupReady

/-! One tuple in the actual selected stream advances its retained input
cursor and returns the occurrence stream/count to their consumer heads.
The complete final store is exposed for the enclosing equation/list loop. -/
namespace NearCubicWires.RepairOrdinary.RowTupleCursorReady
open LocalBitMultitape RecoveryExecution RecoveryRootRound RowMaskPositionParts
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def start (rows : List (List Bool)) (bound : ℕ) : Data := ⟨rows.flatten,0,0,0,[],0,bound,false⟩
def selected (i : Fin 13) : Bool := decide (i=2)
noncomputable def first := MaskedReset.machine RowTupleMaskLoop.machine selected
def capacity (N w M k : ℕ) := RowTupleMaskLoop.budget N w M k
noncomputable def before (N w M : ℕ) (rows : List (List Bool)) (ds : List ℕ) (pre tail : List Bool) (bound : ℕ) :=
  RowTupleMaskLoop.cfg 0 N w M ds.length 1 (pre++RowTupleFilterLoop.word w ds++tail) pre.length (start rows bound)
noncomputable def after (N w M : ℕ) (rows : List (List Bool)) (ds : List ℕ) (pre tail : List Bool) (bound : ℕ) :=
  RowTupleMaskLoop.cfg 3 N w M ds.length 1 (pre++RowTupleFilterLoop.word w ds++tail) (pre.length+2*w*ds.length)
    (RowTupleMaskLoop.fold rows (start rows bound) ds)
noncomputable def input (N w M : ℕ) (rows : List (List Bool)) (ds : List ℕ) (pre tail : List Bool) (bound : ℕ) :=
  ZeroPadding.config (Rewind.Workspace.capacities 13 (capacity N w M ds.length))
    (Rewind.recording (before N w M rows ds pre tail bound) 0)
noncomputable def middleHeads (N w M : ℕ) (rows : List (List Bool)) (ds : List ℕ) (pre tail : List Bool) (bound : ℕ) : Fin 14→ℕ :=
  Fin.addCases (m:=13) (n:=1) (motive:=fun _=>ℕ)
    (fun i=>if selected i then 0 else (after N w M rows ds pre tail bound).heads i) (fun _=>0)
noncomputable def output (N w M : ℕ) (rows : List (List Bool)) (ds : List ℕ) (pre tail : List Bool) (bound : ℕ) : Fin 14→List Bool :=
  Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
    (after N w M rows ds pre tail bound).tapes (fun _=>List.replicate (capacity N w M ds.length) false)
def slots : Fin 1→Fin 14 := fun _=>3
theorem injective : Function.Injective slots := by intro a b _; exact Subsingleton.elim _ _
noncomputable def last := RecoveryFocus.machine slots UnaryTemplate.machine
noncomputable def machine := Composition.machine first last
def budget (N w M k count : ℕ) := 2*capacity N w M k+count+5

theorem output_fields (N w M : ℕ) (rows : List (List Bool)) (ds : List ℕ) (pre tail : List Bool) (bound : ℕ) :
    output N w M rows ds pre tail bound 2=RowTupleMaskLoop.word rows ds ∧
      output N w M rows ds pre tail bound 3=CompareMachine.word (RowTupleMaskLoop.count rows ds) ∧
      middleHeads N w M rows ds pre tail bound 2=0 ∧
      middleHeads N w M rows ds pre tail bound 3=RowTupleMaskLoop.count rows ds+1 := by
  have hf := RowTupleMaskLoop.fold_output rows ds (start rows bound)
  have hout : (RowTupleMaskLoop.fold rows (start rows bound) ds).out=RowTupleMaskLoop.word rows ds := by
    simpa [start] using hf.1
  have hcount : (RowTupleMaskLoop.fold rows (start rows bound) ds).count=RowTupleMaskLoop.count rows ds := by
    simpa [start] using hf.2
  simp [output,middleHeads,after,RowTupleMaskLoop.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,RowTupleMaskBody.cfg,
    RowMaskLookupReusable.cfg,RowMaskConsume.bank,ZeroPadding.config,RowMaskPositionParts.cfg,
    RowMaskPositionParts.tapes,RowMaskPositionParts.heads,RowMaskConsume.capacities,ZeroPadding.pad,
    selected,Fin.addCases,hout,hcount]

theorem first_run (N w M : ℕ) (rows : List (List Bool)) (ds : List ℕ) (pre tail : List Bool) (bound : ℕ)
    (hl : ∀ row∈rows,row.length=N) (hd : ∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M) :
    ∃ r,runFrom first (2*capacity N w M ds.length+2) (input N w M rows ds pre tail bound)=some r ∧
      r.final.heads=middleHeads N w M rows ds pre tail bound ∧
      r.final.tapes=output N w M rows ds pre tail bound ∧ r.steps≤2*capacity N w M ds.length+2 := by
  obtain ⟨time,hbound,ht⟩ := RowTupleMaskLoop.remaining N w M ds.length 0 rows ds
    (pre++RowTupleFilterLoop.word w ds++tail) pre tail (start rows bound)
    (by simp) rfl rfl rfl rfl rfl hl hd hb hM
  have hbudget : time≤capacity N w M ds.length := by unfold capacity RowTupleMaskLoop.budget; nlinarith
  simp only [RowTupleFilterLoop.word_length] at ht
  obtain ⟨base,hbase,bf,bs⟩ := ht.run
    (by simp [RowTupleMaskLoop.machine,RowTupleMaskLoop.cfg,RepeatMachine.machine,
      RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
  have more:=runFrom_moreFuel RowTupleMaskLoop.machine time
    (capacity N w M ds.length-time) _ base hbase
  rw [Nat.add_sub_of_le hbudget] at more
  have bsteps : base.steps≤capacity N w M ds.length := bs.le.trans hbudget
  obtain ⟨r,hr,rf,rs,_⟩ := MaskedReset.workspace_run RowTupleMaskLoop.machine selected _
    (capacity N w M ds.length) _ base more (by
      intro i hi
      have he : i=2 := by simpa only [selected,decide_eq_true_eq] using hi
      subst i; rfl) bsteps
  have ht : 2*base.steps+2≤2*capacity N w M ds.length+2 := by omega
  have more := runFrom_moreFuel first _ (2*capacity N w M ds.length+2-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le ht] at more
  refine ⟨r,more,?_,?_,rs.le.trans ht⟩
  · rw [rf,bf]; rfl
  · rw [rf,bf]; rfl

theorem tuple_run (N w M : ℕ) (rows : List (List Bool)) (ds : List ℕ) (pre tail : List Bool) (bound : ℕ)
    (hl : ∀ row∈rows,row.length=N) (hd : ∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M) :
    ∃ r,runFrom machine (budget N w M ds.length (RowTupleMaskLoop.count rows ds))
      (Composition.restart (input N w M rows ds pre tail bound) machine.start)=some r ∧
      r.final.heads=Function.update (middleHeads N w M rows ds pre tail bound) 3 1 ∧
      r.final.tapes=output N w M rows ds pre tail bound ∧
      r.steps≤budget N w M ds.length (RowTupleMaskLoop.count rows ds) := by
  obtain ⟨a,ha,ah,atapes,_⟩ := first_run N w M rows ds pre tail bound hl hd hb hM
  obtain ⟨base,hbase,bf,_⟩ := RowMaskLookupReady.count_run (RowTupleMaskLoop.count rows ds)
  have fields := output_fields N w M rows ds pre tail bound
  obtain ⟨b,hbRun,be,_⟩ := RecoveryFocus.run_config slots injective UnaryTemplate.machine
    a.final.heads a.final.tapes _ _ base hbase
  have hi : RecoveryFocus.config slots a.final.heads a.final.tapes
      (UnaryTemplate.config 0 (CompareMachine.word (RowTupleMaskLoop.count rows ds))
        (RowTupleMaskLoop.count rows ds+1))=Composition.restart a.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      change a.final.heads 3=_
      rw [ah]; exact fields.2.2.2
    · intro i
      change a.final.tapes 3=_
      rw [atapes]; exact fields.2.1
  rw [hi] at hbRun
  have whole := Composition.run_join first last _ _ _ a b ha hbRun
  have ht : (2*capacity N w M ds.length+2)+1+(RowTupleMaskLoop.count rows ds+2)=
      budget N w M ds.length (RowTupleMaskLoop.count rows ds) := by unfold budget; omega
  rw [ht] at whole
  have hpick (i : Fin 14) : RecoveryFocus.pick slots i=if i=3 then some 0 else none := by
    fin_cases i
    all_goals first | exact RecoveryFocus.pick_slot slots injective 0 | decide
  refine ⟨Composition.joinedReceipt a b,whole,?_,?_,runFrom_steps_le machine _ _ _ whole⟩
  · change b.final.heads=_
    rw [be,bf]
    funext i
    by_cases hi:i=3
    · subst i; simp [RecoveryFocus.config,hpick,UnaryTemplate.config]
    · simp [RecoveryFocus.config,hpick,hi,ah]
  · change b.final.tapes=_
    rw [be,bf]
    funext i
    by_cases hi:i=3
    · subst i
      simpa only [RecoveryFocus.config,hpick,ite_true,UnaryTemplate.config] using fields.2.1.symm
    · simp [RecoveryFocus.config,hpick,hi,atapes]

end NearCubicWires.RepairOrdinary.RowTupleCursorReady
