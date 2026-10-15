import Proof.Supplier.RowMaskLookup
import Proof.Supplier.RowMaskBankClear

/-! Reusable selected-mask lookup: actual positioning, occurrence emission,
local erasure, and a recorded return of only the cache cursor. -/
namespace NearCubicWires.RepairOrdinary.RowMaskLookupReusable
open LocalBitMultitape RecoveryExecution RowMaskPositionParts RowMaskConsume
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def body := Composition.machine RowMaskLookup.machine RowMaskBankClear.machine
def selected (i : Fin 9) : Bool := decide (i=0)
noncomputable def machine := MaskedReset.machine body selected
def capacity (N w M : ℕ) := RowMaskLookup.budget N w M+2*N+4*w+8

def bodyResult (N : ℕ) (rows : List (List Bool)) (bits : List Bool) (x : Data) : Data :=
  {RowMaskLookup.result N rows bits x with index:=0,counter:=0}
def result (bits : List Bool) (x : Data) : Data :=
  {x with
    pos := 0
    index := 0
    counter := 0
    flag := false
    count := x.count + bits.count true
    out := x.out ++ RowMaskLoop.word 0 bits}
def cfg {s : ℕ} (q : Fin s) (N w M : ℕ) (x : Data) : Configuration 10 s :=
  ⟨q,Fin.addCases (m:=9) (n:=1) (motive:=fun _=>ℕ) (heads x) (fun _=>0),
    Fin.addCases (m:=9) (n:=1) (motive:=fun _=>List Bool)
      (bank q N w x).tapes (fun _=>List.replicate (capacity N w M) false)⟩

theorem body_run (N w : ℕ) (rows : List (List Bool)) (bits tail : List Bool) (x : Data)
    (hx : x.source=rows.flatten++bits++tail) (hp : x.pos=0) (hi : x.index=0)
    (hl : ∀ row∈rows,row.length=N) (hn : bits.length=N)
    (hc : x.counter=0) (hd : x.bound=rows.length) (hb : rows.length+1<2^w) :
    ∃ r,runFrom body (capacity N w rows.length) (bank body.start N w x)=some r ∧
      r.final.heads=(bank body.start N w (bodyResult N rows bits x)).heads ∧
      r.final.tapes=(bank body.start N w (bodyResult N rows bits x)).tapes ∧
      r.steps≤capacity N w rows.length := by
  obtain ⟨a,ha,ah,atapes,_⟩ := RowMaskLookup.lookup_run N w rows bits tail x hx hp hi hl hn hc hd hb
  obtain ⟨b,hb,bh,bt,_⟩ := RowMaskBankClear.clear_run N w (RowMaskLookup.result N rows bits x) rfl
  have he : bank RowMaskBankClear.machine.start N w (RowMaskLookup.result N rows bits x)=
      Composition.restart a.final RowMaskBankClear.machine.start := by
    apply configuration_ext
    · rfl
    · exact ah.symm
    · exact atapes.symm
  rw [he] at hb
  have whole := Composition.run_join RowMaskLookup.machine RowMaskBankClear.machine _ _ _ a b ha hb
  have ht : RowMaskLookup.budget N w rows.length+1+(2*N+4*w+7)=capacity N w rows.length := by
    simp only [capacity]; omega
  rw [ht] at whole
  exact ⟨Composition.joinedReceipt a b,whole,bh,bt,runFrom_steps_le body _ _ _ whole⟩

theorem lookup_run (N w M : ℕ) (rows : List (List Bool)) (bits tail : List Bool) (x : Data)
    (hx : x.source=rows.flatten++bits++tail) (hp : x.pos=0) (hi : x.index=0)
    (hl : ∀ row∈rows,row.length=N) (hn : bits.length=N)
    (hc : x.counter=0) (hd : x.bound=rows.length) (hb : rows.length+1<2^w) (hM : rows.length≤M) :
    ∃ r,runFrom machine (2*capacity N w M+2) (cfg machine.start N w M x)=some r ∧
      r.final.heads=(cfg machine.start N w M (result bits x)).heads ∧
      r.final.tapes=(cfg machine.start N w M (result bits x)).tapes ∧
      r.steps≤2*capacity N w M+2 := by
  obtain ⟨base,hbase,bh,bt,bs⟩ := body_run N w rows bits tail x hx hp hi hl hn hc hd hb
  have hcap : base.steps≤capacity N w M := by
    apply bs.trans
    simp only [capacity,RowMaskLookup.budget]
    nlinarith [Nat.mul_le_mul_right (2*N+8*w+15) hM]
  obtain ⟨r,hr,rf,rs,_⟩ := MaskedReset.workspace_run body selected _ (capacity N w M) _ base hbase
    (by intro i hh; have he : i=0 := by simpa only [selected,decide_eq_true_eq] using hh
        subst i; exact hp) hcap
  have he : ZeroPadding.config (Rewind.Workspace.capacities 9 (capacity N w M))
      (Rewind.recording (bank body.start N w x) 0)=cfg machine.start N w M x := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [cfg,ZeroPadding.config,Rewind.Workspace.capacities,
        Rewind.recording,Rewind.config,Fin.addCases,
        bank,RowMaskPositionParts.cfg,ZeroPadding.pad]
  rw [he] at hr
  have hbtime : 2*base.steps+2≤2*capacity N w M+2 := by omega
  have more := runFrom_moreFuel machine (2*base.steps+2) (2*capacity N w M+2-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hbtime] at more
  refine ⟨r,more,?_,?_,by omega⟩
  · rw [rf,bh]
    funext i; fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,cfg,selected,heads,
      bodyResult,RowMaskLookup.result,RowMaskPositionLoop.endpoint,consumed,result,bank,ZeroPadding.config,
      RowMaskPositionParts.cfg,Fin.addCases]
  · rw [rf,bt]
    funext i; fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,cfg,bank,ZeroPadding.config,
      RowMaskPositionParts.cfg,tapes,capacities,bodyResult,RowMaskLookup.result,RowMaskPositionLoop.endpoint,
      consumed,result,Fin.addCases]

end NearCubicWires.RepairOrdinary.RowMaskLookupReusable
