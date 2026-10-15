import Proof.Supplier.RowTupleMaskLoop
import Proof.Supplier.RowMaskLookupReady

/-! The tuple's actual occurrence stream is returned to its first cell and
its counted driver to head1, ready for the common-width equation consumer. -/
namespace NearCubicWires.RepairOrdinary.RowTupleMaskReady
open LocalBitMultitape RecoveryExecution RecoveryRootRound RowMaskPositionParts
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def start (rows : List (List Bool)) : Data := ⟨rows.flatten,0,0,0,[],0,0,false⟩
def selected (i : Fin 13) : Bool := decide (i=2)
noncomputable def first := MaskedReset.machine RowTupleMaskLoop.machine selected
def capacity (N w M k : ℕ) := RowTupleMaskLoop.budget N w M k
noncomputable def before (N w M : ℕ) (rows : List (List Bool)) (ds : List ℕ) (tail : List Bool) :=
  RowTupleMaskLoop.cfg 0 N w M ds.length 1 (RowTupleFilterLoop.word w ds++tail) 0 (start rows)
noncomputable def after (N w M : ℕ) (rows : List (List Bool)) (ds : List ℕ) (tail : List Bool) :=
  RowTupleMaskLoop.cfg 3 N w M ds.length 1 (RowTupleFilterLoop.word w ds++tail) (2*w*ds.length)
    (RowTupleMaskLoop.fold rows (start rows) ds)
noncomputable def input (N w M : ℕ) (rows : List (List Bool)) (ds : List ℕ) (tail : List Bool) :=
  ZeroPadding.config (Rewind.Workspace.capacities 13 (capacity N w M ds.length))
    (Rewind.recording (before N w M rows ds tail) 0)
noncomputable def middleHeads (N w M : ℕ) (rows : List (List Bool)) (ds : List ℕ) (tail : List Bool) : Fin 14→ℕ :=
  Fin.addCases (m:=13) (n:=1) (motive:=fun _=>ℕ)
    (fun i=>if selected i then 0 else (after N w M rows ds tail).heads i) (fun _=>0)
noncomputable def output (N w M : ℕ) (rows : List (List Bool)) (ds : List ℕ) (tail : List Bool) : Fin 14→List Bool :=
  Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
    (after N w M rows ds tail).tapes (fun _=>List.replicate (capacity N w M ds.length) false)
def slots : Fin 1→Fin 14 := fun _=>3
theorem injective : Function.Injective slots := by intro a b _; exact Subsingleton.elim _ _
noncomputable def last := RecoveryFocus.machine slots UnaryTemplate.machine
noncomputable def machine := Composition.machine first last
def budget (N w M k count : ℕ) := 2*capacity N w M k+count+5

theorem output_fields (N w M : ℕ) (rows : List (List Bool)) (ds : List ℕ) (tail : List Bool) :
    output N w M rows ds tail 2=RowTupleMaskLoop.word rows ds ∧
      output N w M rows ds tail 3=CompareMachine.word (RowTupleMaskLoop.count rows ds) ∧
      middleHeads N w M rows ds tail 2=0 ∧
      middleHeads N w M rows ds tail 3=RowTupleMaskLoop.count rows ds+1 := by
  have hf := RowTupleMaskLoop.fold_output rows ds (start rows)
  have hout : (RowTupleMaskLoop.fold rows (start rows) ds).out=RowTupleMaskLoop.word rows ds := by
    simpa [start] using hf.1
  have hcount : (RowTupleMaskLoop.fold rows (start rows) ds).count=RowTupleMaskLoop.count rows ds := by
    simpa [start] using hf.2
  simp [output,middleHeads,after,RowTupleMaskLoop.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,RowTupleMaskBody.cfg,
    RowMaskLookupReusable.cfg,RowMaskConsume.bank,ZeroPadding.config,RowMaskPositionParts.cfg,
    RowMaskPositionParts.tapes,RowMaskPositionParts.heads,RowMaskConsume.capacities,ZeroPadding.pad,
    selected,Fin.addCases,hout,hcount]

theorem first_run (N w M : ℕ) (rows : List (List Bool)) (ds : List ℕ) (tail : List Bool)
    (hl : ∀ row∈rows,row.length=N) (hd : ∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M) :
    ∃ r,runFrom first (2*capacity N w M ds.length+2) (input N w M rows ds tail)=some r ∧
      r.final.heads=middleHeads N w M rows ds tail ∧
      r.final.tapes=output N w M rows ds tail ∧ r.steps≤2*capacity N w M ds.length+2 := by
  obtain ⟨base,hbase,bf,bs⟩ := RowTupleMaskLoop.tuple_run N w M rows ds tail (start rows)
    rfl rfl rfl rfl hl hd hb hM
  obtain ⟨r,hr,rf,rs,_⟩ := MaskedReset.workspace_run RowTupleMaskLoop.machine selected _
    (capacity N w M ds.length) _ base hbase (by
      intro i hi
      have he : i=2 := by simpa only [selected,decide_eq_true_eq] using hi
      subst i; rfl) bs
  have ht : 2*base.steps+2≤2*capacity N w M ds.length+2 := by unfold capacity; omega
  have more := runFrom_moreFuel first _ (2*capacity N w M ds.length+2-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le ht] at more
  refine ⟨r,more,?_,?_,rs.le.trans ht⟩
  · rw [rf,bf]; rfl
  · rw [rf,bf]; rfl

theorem tuple_run (N w M : ℕ) (rows : List (List Bool)) (ds : List ℕ) (tail : List Bool)
    (hl : ∀ row∈rows,row.length=N) (hd : ∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M) :
    ∃ r,runFrom machine (budget N w M ds.length (RowTupleMaskLoop.count rows ds))
      (Composition.restart (input N w M rows ds tail) machine.start)=some r ∧
      r.final.tapes 2=RowTupleMaskLoop.word rows ds ∧
      r.final.tapes 3=CompareMachine.word (RowTupleMaskLoop.count rows ds) ∧
      r.final.heads 2=0 ∧ r.final.heads 3=1 ∧
      r.steps≤budget N w M ds.length (RowTupleMaskLoop.count rows ds) := by
  obtain ⟨a,ha,ah,atapes,_⟩ := first_run N w M rows ds tail hl hd hb hM
  obtain ⟨base,hbase,bf,_⟩ := RowMaskLookupReady.count_run (RowTupleMaskLoop.count rows ds)
  have fields := output_fields N w M rows ds tail
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
  have hnone : RecoveryFocus.pick slots (2 : Fin 14)=none := by decide
  have hsome : RecoveryFocus.pick slots (3 : Fin 14)=some 0 := RecoveryFocus.pick_slot slots injective 0
  refine ⟨Composition.joinedReceipt a b,whole,?_,?_,?_,?_,runFrom_steps_le machine _ _ _ whole⟩
  · change b.final.tapes 2=_
    rw [be]; simp only [RecoveryFocus.config,hnone,atapes]; exact fields.1
  · change b.final.tapes 3=_
    rw [be,bf]; simp only [RecoveryFocus.config,hsome]; rfl
  · change b.final.heads 2=_
    rw [be]; simp only [RecoveryFocus.config,hnone,ah]; exact fields.2.2.1
  · change b.final.heads 3=_
    rw [be,bf]; simp only [RecoveryFocus.config,hsome]; rfl

end NearCubicWires.RepairOrdinary.RowTupleMaskReady
