import Proof.Supplier.RowTupleEnumeration

/-! The enumerator allocates its short scratch tapes by real writes during
execution. Its initial workspace and flags are empty, and driver positioning
and true flags are supplied by one physical transition. -/
namespace NearCubicWires.RepairOrdinary.RowTupleColdLogs
open LocalBitMultitape RecoveryExecution RowTupleOutputParts RowTupleEnumeration
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacities (w k : ℕ) : Fin 18→ℕ :=
  ![0,0,0,0,1,4*w+4,0,1,1,0,2*w+1,4*w+3,0,RowTupleFilterReusable.time w k,0,0,2*(w*k)+3,0]
def blank (i : Fin 18) : Bool := decide (i=4 ∨ i=5 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=13 ∨ i=15 ∨ i=16)
noncomputable def tapes (w k M : ℕ) (out : List Bool) : Fin 18→List Bool :=
  fun i=>if blank i then [] else (cfg RowTupleOutputLoop.machine.start w k (start w k M) true out).tapes i
def heads (out : List Bool) : Fin 18→ℕ := fun i=>if i=17 then out.length else 0
noncomputable def input {s : ℕ} (q : Fin s) (w k M : ℕ) (out : List Bool) : Configuration 18 s :=
  ⟨q,heads out,tapes w k M out⟩
def flagMachine : Machine 18 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,
    fun i=>if i=9 ∨ i=15 then some true else none,
    fun i=>if i=2 ∨ i=12 then .right else .stay⟩ else none
noncomputable def prepared {s : ℕ} (q : Fin s) (w k M : ℕ) (out : List Bool) : Configuration 18 s :=
  ⟨q,(cfg RowTupleOutputLoop.machine.start w k (start w k M) true out).heads,
    fun i=>if i=9 ∨ i=15 then [true] else tapes w k M out i⟩
noncomputable def machine := Composition.machine flagMachine RowTupleOutputLoop.machine

theorem flag_run (w k M : ℕ) (out : List Bool) :
    ∃ r,runFrom flagMachine 1 (input 0 w k M out)=some r ∧
      r.final=prepared 1 w k M out ∧ r.steps=1 := by
  have hs : step flagMachine (input 0 w k M out)=some (prepared 1 w k M out) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,input,heads,prepared,cfg,
        TapeEmbedding.config,Fin.addCases,RowTupleAdvance.cfg,RowTupleFilterReusable.cfg,RowTupleFilterReusable.heads]
    · funext i; fin_cases i <;> simp [applyAction,input,heads,prepared,tapes,blank,writeTapeBit]
  exact (Timed.single (by rfl) hs).run (by rfl)

theorem pad_prepared (w k M : ℕ) (out : List Bool) :
    ZeroPadding.config (capacities w k) (prepared RowTupleOutputLoop.machine.start w k M out)=
      cfg RowTupleOutputLoop.machine.start w k (start w k M) true out := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i <;> simp [ZeroPadding.config,capacities,prepared,tapes,blank,
      ZeroPadding.pad,cfg,TapeEmbedding.config,Fin.addCases,RowTupleAdvance.cfg,RowTupleAdvance.extra,
      RowTupleFilterReusable.cfg,RowTupleFilterReusable.tapes,RowTupleFilterParts.tapes,start,RowTupleFilterMeaning.initial]

theorem enumerate_run (w k M : ℕ) (out : List Bool) (hM : 0<M) (hMw : M≤2^w) :
    ∃ r,runFrom machine (time w k+2) (input machine.start w k M out)=some r ∧
      r.final.tapes 0=frame (SignedSortKey.binary (w*k+1) (2^(w*k))) ∧
      r.final.tapes 17=out++word w k M ∧
      r.final.heads=(cfg RowTupleOutputLoop.machine.start w k (result w k M) false (out++word w k M)).heads ∧
      r.steps≤time w k+2 := by
  obtain ⟨base,hbase,bh,_,b0,b17,bs⟩ := RowTupleEnumeration.enumerate_run w k M out hM hMw
  rw [←pad_prepared] at hbase
  obtain ⟨b,hb,bf,bsteps,_⟩ := ZeroPadding.run_unpad RowTupleOutputLoop.machine (capacities w k)
    (time w k) (prepared RowTupleOutputLoop.machine.start w k M out) base hbase
  have b0' := congrArg (fun c=>c.tapes 0) bf
  have b17' := congrArg (fun c=>c.tapes 17) bf
  have bh' := congrArg Configuration.heads bf
  simp only [ZeroPadding.config,capacities,Matrix.cons_val_zero,ZeroPadding.pad_zero] at b0'
  have hout : b.final.tapes 17=out++word w k M := by
    have he : ZeroPadding.pad 0 (b.final.tapes 17)=base.final.tapes 17 := b17'
    simpa only [ZeroPadding.pad_zero] using he.trans b17
  obtain ⟨a,ha,af,as⟩ := flag_run w k M out
  have hi : prepared RowTupleOutputLoop.machine.start w k M out=
      Composition.restart a.final RowTupleOutputLoop.machine.start := by rw [af]; rfl
  rw [hi] at hb
  have h := Composition.run_join flagMachine RowTupleOutputLoop.machine _ _ _ a b ha hb
  have he : 1+1+time w k=time w k+2 := by omega
  rw [he] at h
  exact ⟨Composition.joinedReceipt a b,h,b0'.trans b0,hout,bh'.trans bh,
    by change a.steps+1+b.steps≤_; rw [as,bsteps]; omega⟩

end NearCubicWires.RepairOrdinary.RowTupleColdLogs
