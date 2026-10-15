import Proof.Supplier.RowTupleFilterParts

/-! The executed digit body reads, checks the bound and strict ordering,
updates its accumulated validity flag, and saves the current digit. -/
namespace NearCubicWires.RepairOrdinary.RowTupleFilterBody
open LocalBitMultitape RecoveryExecution RowTupleFilterParts SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def bounded := Composition.machine readMachine (compareMachine false)
noncomputable def ordered := Composition.machine bounded (compareMachine true)
noncomputable def guarded := Composition.machine ordered updateMachine
noncomputable def machine := Composition.machine guarded copyMachine
def afterRead (x : Data) (d : ℕ) : Data := {x with current:=d}
def afterBound (x : Data) (d : ℕ) := compared false (afterRead x d)
def afterOrder (x : Data) (d : ℕ) := compared true (afterBound x d)
def afterGuard (x : Data) (d : ℕ) := updated (afterOrder x d)
def advance (x : Data) (d : ℕ) : Data := {afterGuard x d with previous:=d}

theorem restart_eq {s t : ℕ} (c : Configuration 12 s) (q : Fin t) (pos w : ℕ) (x : Data)
    (hh : c.heads=heads pos) (ht : c.tapes=tapes w x) :
    Composition.restart c q=cfg q pos w x := by
  apply configuration_ext
  · rfl
  · exact hh
  · exact ht

theorem body_run (pre tail : List Bool) (w d : ℕ) (x : Data)
    (hx : x.source=pre++Streaming.marks (binary w d)++tail)
    (hd : d<2^w) (hb : x.bound<2^w) (hp : x.previous<2^w) :
    ∃ r,runFrom machine (20*w+31) (cfg machine.start pre.length w x)=some r ∧
      r.final.heads=heads (pre.length+2*w) ∧
      r.final.tapes=tapes w (advance x d) ∧ r.steps=20*w+31 := by
  obtain ⟨a,ha,af,as⟩ := read_run pre tail w d x hx
  obtain ⟨b,hbRun,bh,bt,bs⟩ := compare_run false (pre.length+2*w) w (afterRead x d) hd hb hp
  have hi : cfg (compareMachine false).start (pre.length+2*w) w (afterRead x d)=
      Composition.restart a.final (compareMachine false).start := by rw [af]; rfl
  rw [hi] at hbRun
  let ab := Composition.joinedReceipt a b
  have hab := Composition.run_join readMachine (compareMachine false) _ _ _ a b ha hbRun
  obtain ⟨c,hc,ch,ct,cs⟩ := compare_run true (pre.length+2*w) w (afterBound x d) hd hb hp
  have hcIn : Composition.restart ab.final (compareMachine true).start=
      cfg (compareMachine true).start (pre.length+2*w) w (afterBound x d) :=
    restart_eq _ _ _ _ _ bh bt
  rw [←hcIn] at hc
  let abc := Composition.joinedReceipt ab c
  have habc := Composition.run_join bounded (compareMachine true) _ _ _ ab c hab hc
  obtain ⟨e,he,ef,es⟩ := update_run (pre.length+2*w) w (afterOrder x d)
  have heIn : Composition.restart abc.final updateMachine.start=
      cfg 0 (pre.length+2*w) w (afterOrder x d) := restart_eq _ _ _ _ _ ch ct
  rw [←heIn] at he
  let abce := Composition.joinedReceipt abc e
  have habce := Composition.run_join ordered updateMachine _ _ _ abc e habc he
  obtain ⟨f,hf,fh,ft,fs⟩ := copy_run (pre.length+2*w) w (afterGuard x d)
  have hfIn : Composition.restart abce.final copyMachine.start=
      cfg copyMachine.start (pre.length+2*w) w (afterGuard x d) := by
    change Composition.restart e.final copyMachine.start=_
    rw [ef]
    rfl
  rw [←hfIn] at hf
  have whole := Composition.run_join guarded copyMachine _ _ _ abce f habce hf
  have htime : (((4*w+2+1+(4*w+8))+1+(4*w+8))+1+1)+1+(8*w+8)=20*w+31 := by omega
  rw [htime] at whole
  refine ⟨Composition.joinedReceipt abce f,whole,fh,ft,?_⟩
  change (((a.steps+1+b.steps)+1+c.steps)+1+e.steps)+1+f.steps=20*w+31
  rw [as,bs,cs,es,fs,htime]

theorem advance_fields (x : Data) (d : ℕ) :
    (advance x d).source=x.source ∧ (advance x d).bound=x.bound ∧
    (advance x d).current=d ∧ (advance x d).previous=d ∧ (advance x d).seen=true := by
  simp [advance,afterGuard,afterOrder,afterBound,afterRead,compared,updated]

theorem advance_good (x : Data) (d : ℕ) :
    (advance x d).good=true ↔ x.good=true ∧ (x.seen=true → x.previous<d) ∧ d≤x.bound := by
  simp only [advance,afterGuard,afterOrder,afterBound,afterRead,compared,Bool.false_eq_true,
    ↓reduceIte,updated,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
  cases x.seen <;> simp [and_assoc]

end NearCubicWires.RepairOrdinary.RowTupleFilterBody
