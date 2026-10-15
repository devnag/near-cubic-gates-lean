import Proof.Supplier.RowMaskLookupReusable
import Proof.Supplier.RowMaskMeaning

/-! Selected-mask output ready for the common coefficient consumer. The
occurrence word is physically rewound, and its actual count returns to head1. -/
namespace NearCubicWires.RepairOrdinary.RowMaskLookupReady
open LocalBitMultitape RecoveryExecution RecoveryRootRound RowMaskPositionParts RowMaskConsume
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def start (rows : List (List Bool)) (bits tail : List Bool) : Data :=
  ⟨rows.flatten++bits++tail,0,0,0,[],0,rows.length,false⟩
def selected (i : Fin 9) : Bool := decide (i=0 ∨ i=2)
noncomputable def first := MaskedReset.machine RowMaskLookupReusable.body selected
def capacity := RowMaskLookupReusable.capacity
def input {s : ℕ} (q : Fin s) (N w M : ℕ) (rows : List (List Bool)) (bits tail : List Bool) :=
  RowMaskLookupReusable.cfg q N w M (start rows bits tail)
def result (rows : List (List Bool)) (bits tail : List Bool) :=
  RowMaskLookupReusable.result bits (start rows bits tail)
def output (N w M : ℕ) (rows : List (List Bool)) (bits tail : List Bool) : Fin 10→List Bool :=
  (RowMaskLookupReusable.cfg (0 : Fin 1) N w M (result rows bits tail)).tapes
def heads : Fin 10→ℕ := ![0,1,0,1,1,0,0,0,0,0]
def middleHeads (count : ℕ) : Fin 10→ℕ := ![0,1,0,count+1,1,0,0,0,0,0]

theorem first_run (N w M : ℕ) (rows : List (List Bool)) (bits tail : List Bool)
    (hl : ∀ row∈rows,row.length=N) (hn : bits.length=N)
    (hb : rows.length+1<2^w) (hM : rows.length≤M) :
    ∃ r,runFrom first (2*capacity N w M+2) (input first.start N w M rows bits tail)=some r ∧
      r.final.heads=middleHeads (bits.count true) ∧ r.final.tapes=output N w M rows bits tail ∧
      r.steps≤2*capacity N w M+2 := by
  obtain ⟨base,hbase,bh,bt,bs⟩ := RowMaskLookupReusable.body_run N w rows bits tail
    (start rows bits tail) rfl rfl rfl hl hn rfl rfl hb
  have hcap : base.steps≤capacity N w M := by
    apply bs.trans
    simp only [capacity,RowMaskLookupReusable.capacity,RowMaskLookup.budget]
    nlinarith [Nat.mul_le_mul_right (2*N+8*w+15) hM]
  obtain ⟨r,hr,rf,rs,_⟩ := MaskedReset.workspace_run RowMaskLookupReusable.body selected _
    (capacity N w M) _ base hbase (by
      intro i hi
      have he : i=0 ∨ i=2 := by simpa only [selected,decide_eq_true_eq] using hi
      rcases he with rfl | rfl <;> rfl) hcap
  have he : ZeroPadding.config (Rewind.Workspace.capacities 9 (capacity N w M))
      (Rewind.recording (bank RowMaskLookupReusable.body.start N w (start rows bits tail)) 0)=
      input first.start N w M rows bits tail := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [input,RowMaskLookupReusable.cfg,ZeroPadding.config,
        Rewind.Workspace.capacities,Rewind.recording,Rewind.config,Fin.addCases,
        bank,RowMaskPositionParts.cfg,ZeroPadding.pad,capacity]
  rw [he] at hr
  have ht : 2*base.steps+2≤2*capacity N w M+2 := by omega
  have more := runFrom_moreFuel first _ (2*capacity N w M+2-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le ht] at more
  refine ⟨r,more,?_,?_,by omega⟩
  · rw [rf,bh]
    funext i; fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,middleHeads,selected,
      RowMaskLookupReusable.bodyResult,RowMaskLookup.result,RowMaskPositionLoop.endpoint,consumed,
      bank,ZeroPadding.config,RowMaskPositionParts.cfg,RowMaskPositionParts.heads,start,Fin.addCases]
  · rw [rf,bt]
    funext i; fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,output,RowMaskLookupReusable.cfg,
      bank,ZeroPadding.config,RowMaskPositionParts.cfg,tapes,capacities,
      RowMaskLookupReusable.bodyResult,RowMaskLookup.result,RowMaskPositionLoop.endpoint,
      consumed,result,RowMaskLookupReusable.result,start,Fin.addCases,capacity]

def slots : Fin 1→Fin 10 := fun _=>3
theorem injective : Function.Injective slots := by intro a b _; exact Subsingleton.elim _ _
noncomputable def last := RecoveryFocus.machine slots UnaryTemplate.machine
noncomputable def machine := Composition.machine first last
def budget (N w M : ℕ) := 2*capacity N w M+N+5
theorem pick (i : Fin 10) : RecoveryFocus.pick slots i=(if i=3 then some 0 else none) := by
  fin_cases i
  all_goals first | exact RecoveryFocus.pick_slot slots injective 0 | decide

theorem count_run (count : ℕ) :
    ∃ r,runFrom UnaryTemplate.machine (count+2) (UnaryTemplate.config 0 (CompareMachine.word count) (count+1))=some r ∧
      r.final=UnaryTemplate.config 2 (CompareMachine.word count) 1 ∧ r.steps=count+2 := by
  have hp := UnaryTemplate.return_prefix (CompareMachine.word count) count (by rfl)
    (by intro k hk; simp [CompareMachine.read_mark,hk])
  have h := Prefix.step (by simp : (UnaryTemplate.config 0 (CompareMachine.word count) (count+1)).tapeCells≤
      (CompareMachine.word count).length) (by rfl) (UnaryTemplate.start_step (CompareMachine.word count) count) hp
  obtain ⟨r,hr,rf,rs,_⟩ := h.run (by rfl) (by simp)
  exact ⟨r,by simpa [Nat.add_assoc] using hr,rf,by omega⟩

theorem lookup_run (N w M : ℕ) (rows : List (List Bool)) (bits tail : List Bool)
    (hl : ∀ row∈rows,row.length=N) (hn : bits.length=N)
    (hb : rows.length+1<2^w) (hM : rows.length≤M) :
    ∃ r,runFrom machine (budget N w M) (input machine.start N w M rows bits tail)=some r ∧
      r.final.heads=heads ∧ r.final.tapes=output N w M rows bits tail ∧ r.steps≤budget N w M := by
  obtain ⟨a,ha,ah,atapes,_⟩ := first_run N w M rows bits tail hl hn hb hM
  obtain ⟨base,hbase,bf,_⟩ := count_run (bits.count true)
  obtain ⟨b,hbRun,be,_⟩ := RecoveryFocus.run_config slots injective UnaryTemplate.machine
    a.final.heads a.final.tapes _ _ base hbase
  have hi : RecoveryFocus.config slots a.final.heads a.final.tapes
      (UnaryTemplate.config 0 (CompareMachine.word (bits.count true)) (bits.count true+1))=
      Composition.restart a.final last.start := by
    apply WilliamsSourceCrop.focus_same slots (Composition.restart a.final last.start)
    · intro i
      change a.final.heads 3=bits.count true+1
      rw [ah]; rfl
    · intro i
      change a.final.tapes 3=CompareMachine.word (bits.count true)
      rw [atapes]
      simp [output,RowMaskLookupReusable.cfg,bank,ZeroPadding.config,RowMaskPositionParts.cfg,
        tapes,capacities,result,RowMaskLookupReusable.result,start,Fin.addCases]
  rw [hi] at hbRun
  have whole := Composition.run_join first last _ _ _ a b ha hbRun
  have hcount : bits.count true≤N := by simpa only [hn] using List.count_le_length (a:=true) (l:=bits)
  have ht : (2*capacity N w M+2)+1+(bits.count true+2)≤budget N w M := by unfold budget; omega
  have more := runFrom_moreFuel machine _
    (budget N w M-((2*capacity N w M+2)+1+(bits.count true+2))) _ (Composition.joinedReceipt a b) whole
  rw [Nat.add_sub_of_le ht] at more
  refine ⟨Composition.joinedReceipt a b,more,?_,?_,runFrom_steps_le machine _ _ _ more⟩
  · change b.final.heads=_
    rw [be,bf]
    funext i; fin_cases i <;> simp [RecoveryFocus.config,pick,UnaryTemplate.config,ah,middleHeads,heads]
  · change b.final.tapes=_
    rw [be,bf]
    funext i; fin_cases i <;> simp [RecoveryFocus.config,pick,UnaryTemplate.config,atapes,output,
      RowMaskLookupReusable.cfg,bank,ZeroPadding.config,RowMaskPositionParts.cfg,tapes,capacities,
      result,RowMaskLookupReusable.result,start,Fin.addCases]

end NearCubicWires.RepairOrdinary.RowMaskLookupReady
