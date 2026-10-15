import Proof.Supplier.RowTupleFilterReusable

/-! Each candidate begins with two physical flag writes, then runs the
reusable tuple filter. Neither its saved digits nor its work bank is rebuilt. -/
namespace NearCubicWires.RepairOrdinary.RowTupleCandidate
open LocalBitMultitape RecoveryExecution RowTupleFilterParts RowTupleFilterBody
open RowTupleFilterMeaning RowTupleFilterReusable SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def restarted (x : Data) : Data := {x with seen:=false,good:=true}
def startMachine : Machine 14 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,
    fun i=>if i=8 then some false else if i=9 then some true else none,fun _=>.stay⟩ else none
noncomputable def machine := Composition.machine startMachine RowTupleFilterReusable.machine

theorem start_run (w k : ℕ) (x : Data) :
    ∃ r,runFrom startMachine 1 (RowTupleFilterReusable.cfg 0 w k x)=some r ∧
      r.final=RowTupleFilterReusable.cfg 1 w k (restarted x) ∧ r.steps=1 := by
  have hs : step startMachine (RowTupleFilterReusable.cfg 0 w k x)=
      some (RowTupleFilterReusable.cfg 1 w k (restarted x)) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [RowTupleFilterReusable.cfg,RowTupleFilterReusable.tapes,
        RowTupleFilterReusable.heads,RowTupleFilterParts.tapes,restarted,applyAction,writeTapeBit,Fin.addCases]
  exact (Timed.single (by rfl) hs).run (by rfl)

theorem candidate_run (w k n M : ℕ) (x : Data)
    (hn : n<2^(w*k)) (hM : 0<M) (hMw : M≤2^w)
    (hx : x.source=frame (binary (w*k+1) n)) (hb : x.bound=M-1) (hp : x.previous<2^w) :
    ∃ r,runFrom machine (k*(40*w+68)+10) (RowTupleFilterReusable.cfg machine.start w k x)=some r ∧
      r.final.heads=RowTupleFilterReusable.heads ∧
      r.final.tapes=RowTupleFilterReusable.tapes w k (fold (restarted x) (RowTupleDigits.digits w k n)) ∧
      r.final.tapes 9=[RowTupleSubsets.valid M (RowTupleDigits.digits w k n)] ∧
      r.final.tapes 0=x.source ∧ r.steps=k*(40*w+68)+10 := by
  obtain ⟨a,ha,af,as⟩ := start_run w k x
  have hsource : (restarted x).source=RowTupleFilterLoop.word w (RowTupleDigits.digits w k n)++frame [false] := by
    change x.source=_
    rw [hx,counter_word w k n hn]
  obtain ⟨b,hbRun,bh,bt,bs⟩ := RowTupleFilterReusable.scan_run w (RowTupleDigits.digits w k n)
    (restarted x) (frame [false]) hsource (RowTupleDigits.digits_bound w k n)
    (by change x.bound<2^w; rw [hb]; omega) hp
  rw [RowTupleDigits.digits_length] at hbRun bt bs
  have hi : RowTupleFilterReusable.cfg RowTupleFilterReusable.machine.start w k (restarted x)=
      Composition.restart a.final RowTupleFilterReusable.machine.start := by rw [af]; rfl
  rw [hi] at hbRun
  have whole := Composition.run_join startMachine RowTupleFilterReusable.machine _ _ _ a b ha hbRun
  have ht : 1+1+(k*(40*w+68)+8)=k*(40*w+68)+10 := by omega
  rw [ht] at whole
  refine ⟨Composition.joinedReceipt a b,whole,bh,bt,?_,?_,?_⟩
  · change b.final.tapes 9=_
    rw [bt]
    change [(fold (restarted x) (RowTupleDigits.digits w k n)).good]=_
    rw [flag_meaning w k n M (restarted x) hM hb rfl rfl]
  · change b.final.tapes 0=_
    rw [bt]
    exact fold_source (restarted x) _
  · change a.steps+1+b.steps=_
    rw [as,bs,ht]

end NearCubicWires.RepairOrdinary.RowTupleCandidate
