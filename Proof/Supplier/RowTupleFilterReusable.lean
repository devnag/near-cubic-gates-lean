import Proof.Supplier.RowTupleFilterLoop

/-! Rewind only the tuple source after its executed digit scan. All short
fields, result flag, degree and width drivers remain in the same bank. -/
namespace NearCubicWires.RepairOrdinary.RowTupleFilterReusable
open LocalBitMultitape RecoveryExecution RowTupleFilterParts RowTupleFilterBody
open RowTupleFilterMeaning SignedSortKey RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def time (w k : ℕ) := k*(20*w+34)+3
def selected (i : Fin 13) : Bool := decide (i=0)
noncomputable def machine := MaskedReset.machine RowTupleFilterLoop.machine selected
def heads : Fin 14→ℕ := ![0,0,1,0,0,0,0,0,0,0,0,0,1,0]
def tapes (w k : ℕ) (x : Data) : Fin 14→List Bool :=
  Fin.addCases (m:=12) (n:=2) (motive:=fun _=>List Bool) (RowTupleFilterParts.tapes w x)
    ![CompareMachine.word k,List.replicate (time w k) false]
def cfg {s : ℕ} (q : Fin s) (w k : ℕ) (x : Data) : Configuration 14 s :=
  ⟨q,heads,tapes w k x⟩

theorem scan_run (w : ℕ) (ds : List ℕ) (x : Data) (tail : List Bool)
    (hx : x.source=RowTupleFilterLoop.word w ds++tail) (hd : ∀ d∈ds,d<2^w)
    (hb : x.bound<2^w) (hp : x.previous<2^w) :
    ∃ r,runFrom machine (ds.length*(40*w+68)+8) (cfg machine.start w ds.length x)=some r ∧
      r.final.heads=heads ∧ r.final.tapes=tapes w ds.length (fold x ds) ∧
      r.steps=ds.length*(40*w+68)+8 := by
  obtain ⟨base,hbase,bf,bs⟩ := RowTupleFilterLoop.scan_run w ds x tail hx hd hb hp
  obtain ⟨r,hr,rf,rs,_⟩ := MaskedReset.workspace_run RowTupleFilterLoop.machine selected _
    (time w ds.length) _ base hbase
    (by intro i hi; have he : i=0 := by simpa only [selected,decide_eq_true_eq] using hi
        subst i; rfl) (by rw [bs]; rfl)
  have hin : ZeroPadding.config (Rewind.Workspace.capacities 13 (time w ds.length))
      (Rewind.recording (RowTupleFilterLoop.cfg 0 0 1 w ds.length x) 0)=
      cfg machine.start w ds.length x := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,Rewind.Workspace.capacities,
        Rewind.recording,Rewind.config,RowTupleFilterLoop.cfg,RepeatMachine.cfg,controlConfig,
        TapeEmbedding.config,RowTupleFilterParts.cfg,cfg,tapes,Fin.addCases,ZeroPadding.pad]
  rw [hin,bs] at hr
  have he : 2*(ds.length*(20*w+34)+3)+2=ds.length*(40*w+68)+8 := by ring
  rw [he] at hr
  refine ⟨r,hr,?_,?_,by rw [rs,bs,he]⟩
  · rw [rf,bf]
    funext i
    fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,RowTupleFilterLoop.cfg,
      RepeatMachine.cfg,controlConfig,TapeEmbedding.config,RowTupleFilterParts.cfg,
      RowTupleFilterParts.heads,selected,heads,Fin.addCases]
  · rw [rf,bf]
    funext i
    fin_cases i <;> rfl

theorem counter_word (w k n : ℕ) (hn : n<2^(w*k)) :
    frame (binary (w*k+1) n)=RowTupleFilterLoop.word w (RowTupleDigits.digits w k n)++frame [false] := by
  have he := RowTupleDigits.binary_encode w (RowTupleDigits.digits w k n) (RowTupleDigits.digits_bound w k n)
  rw [RowTupleDigits.digits_length,RowTupleDigits.encode_digits w k n hn] at he
  have hb : binary (w*k+1) n=binary (w*k) n++[false] := by
    simpa using (RowFieldPadding.binary_extend (w*k) (w*k+1) n (by omega) hn).symm
  rw [hb,Streaming.frame_append,he]
  simp only [RowTupleFilterLoop.word,Streaming.marks,List.flatMap_assoc]

theorem flag_meaning (w k n M : ℕ) (x : Data) (hM : 0<M) (hx : x.bound=M-1)
    (hs : x.seen=false) (hg : x.good=true) :
    (fold x (RowTupleDigits.digits w k n)).good=RowTupleSubsets.valid M (RowTupleDigits.digits w k n) := by
  apply Bool.eq_iff_iff.mpr
  rw [fold_good,RowTupleSubsets.valid_iff,hs,hg,hx]
  simp only [Bool.false_eq_true,false_implies,and_true,true_and]
  constructor
  · rintro ⟨hp,hb⟩
    exact ⟨hp,fun d hd=>by have h:=hb d hd; omega⟩
  · rintro ⟨hp,hb⟩
    exact ⟨hp,fun d hd=>by have h:=hb d hd; omega⟩

end NearCubicWires.RepairOrdinary.RowTupleFilterReusable
