import Proof.Supplier.RowTupleMaskBody

/-! The short degree driver executes every selected monomial lookup in
tuple order. The physical occurrence stream and count accumulate in place. -/
namespace NearCubicWires.RepairOrdinary.RowTupleMaskLoop
open LocalBitMultitape RecoveryExecution SignedSortKey RowMaskPositionParts
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def mask (rows : List (List Bool)) (d : ℕ) := (rows[d]?).getD []
def advance (rows : List (List Bool)) (x : Data) (d : ℕ) :=
  RowMaskLookupReusable.result (mask rows d) {x with bound:=d}
def fold (rows : List (List Bool)) (x : Data) : List ℕ→Data
  | []=>x
  | d::ds=>fold rows (advance rows x d) ds
def word (rows : List (List Bool)) (ds : List ℕ) := ds.flatMap (fun d=>RowMaskLoop.word 0 (mask rows d))
def count (rows : List (List Bool)) (ds : List ℕ) := (ds.map (fun d=>(mask rows d).count true)).sum
noncomputable def machine := RepeatMachine.machine RowTupleMaskBody.machine (fun _ _=>true)
noncomputable def cfg (phase : Fin 5) (N w M k driver : ℕ) (tuple : List Bool) (pos : ℕ) (x : Data) :=
  RepeatMachine.cfg phase (RowTupleMaskBody.cfg RowTupleMaskBody.machine.start N w M tuple pos x) k driver
def budget (N w M k : ℕ) := k*(RowTupleMaskBody.budget N w M+3)+3

theorem cache_split (rows : List (List Bool)) (d : ℕ) (hd : d<rows.length) :
    rows.flatten=(rows.take d).flatten++mask rows d++(rows.drop (d+1)).flatten := by
  have h := congrArg List.flatten (List.take_append_drop (d+1) rows)
  rw [List.take_succ_eq_append_getElem hd] at h
  simpa only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,
    mask,List.getElem?_eq_getElem hd,Option.getD_some,List.append_assoc] using h.symm

theorem digit_run (N w M d : ℕ) (rows : List (List Bool)) (tuple pre tail : List Bool) (x : Data)
    (ht : tuple=pre++Streaming.marks (binary w d)++tail)
    (hx : x.source=rows.flatten) (hp : x.pos=0) (hi : x.index=0) (hc : x.counter=0)
    (hl : ∀ row∈rows,row.length=N) (hd : d<rows.length) (hb : rows.length<2^w) (hM : rows.length≤M) :
    ∃ r,runFrom RowTupleMaskBody.machine (RowTupleMaskBody.budget N w M)
      (RowTupleMaskBody.cfg RowTupleMaskBody.machine.start N w M tuple pre.length x)=some r ∧
      r.final.heads=(RowTupleMaskBody.cfg RowTupleMaskBody.machine.start N w M tuple (pre.length+2*w)
        (advance rows x d)).heads ∧
      r.final.tapes=(RowTupleMaskBody.cfg RowTupleMaskBody.machine.start N w M tuple (pre.length+2*w)
        (advance rows x d)).tapes ∧ r.steps≤RowTupleMaskBody.budget N w M := by
  have hlen : (rows.take d).length=d := List.length_take_of_le hd.le
  have hs : x.source=(rows.take d).flatten++mask rows d++(rows.drop (d+1)).flatten :=
    hx.trans (cache_split rows d hd)
  have hbits : (mask rows d).length=N := by
    simp only [mask,List.getElem?_eq_getElem hd,Option.getD_some]
    exact hl _ (List.getElem_mem hd)
  have h := RowTupleMaskBody.body_run N w M (rows.take d) (mask rows d) (rows.drop (d+1)).flatten
    tuple pre tail x (by simpa only [hlen] using ht) hs hp hi
    (by intro row hr; exact hl row (List.mem_of_mem_take hr)) hbits hc
    (by rw [hlen]; omega) (by rw [hlen]; omega)
  simpa only [hlen,advance] using h

theorem remaining (N w M k j : ℕ) (rows : List (List Bool)) (ds : List ℕ)
    (tuple pre tail : List Bool) (x : Data) (hj : j+ds.length=k)
    (ht : tuple=pre++RowTupleFilterLoop.word w ds++tail)
    (hx : x.source=rows.flatten) (hp : x.pos=0) (hi : x.index=0) (hc : x.counter=0)
    (hl : ∀ row∈rows,row.length=N) (hd : ∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M) :
    ∃ time,time≤ds.length*(RowTupleMaskBody.budget N w M+2)+k+3 ∧
      Timed machine time (cfg 0 N w M k (j+1) tuple pre.length x)
        (cfg 3 N w M k 1 tuple (pre.length+(RowTupleFilterLoop.word w ds).length) (fold rows x ds)) := by
  induction ds generalizing j pre x with
  | nil =>
    have he : j=k := by simpa using hj
    subst j
    refine ⟨k+3,by simp,?_⟩
    simpa only [machine,cfg,fold,RowTupleFilterLoop.word,List.flatMap_nil,List.length_nil,Nat.add_zero] using
      RepeatMachine.exhaust RowTupleMaskBody.machine (fun _ _=>true)
        (RowTupleMaskBody.cfg RowTupleMaskBody.machine.start N w M tuple pre.length x) k
  | cons d ds ih =>
    have hd0 := hd d (by simp)
    have htuple : tuple=pre++Streaming.marks (binary w d)++(RowTupleFilterLoop.word w ds++tail) := by
      simpa only [RowTupleFilterLoop.word,List.flatMap_cons,List.append_assoc] using ht
    obtain ⟨r,hr,rh,rt,rs⟩ := digit_run N w M d rows tuple pre (RowTupleFilterLoop.word w ds++tail)
      x htuple hx hp hi hc hl hd0 hb hM
    have hstep := RepeatMachine.iteration RowTupleMaskBody.machine (fun _ _=>true)
      (RowTupleMaskBody.cfg RowTupleMaskBody.machine.start N w M tuple pre.length x) k j r
      (by rfl) (by simp only [List.length_cons] at hj; omega) hr
    simp only [↓reduceIte] at hstep
    have he := RowOccurrenceLoop.cfg_eq 0 r.final
      (RowTupleMaskBody.cfg RowTupleMaskBody.machine.start N w M tuple (pre.length+2*w) (advance rows x d))
      k (j+2) rh rt
    rw [he] at hstep
    have hnext : tuple=(pre++Streaming.marks (binary w d))++RowTupleFilterLoop.word w ds++tail := by
      simpa only [List.append_assoc] using htuple
    obtain ⟨time,htime,htail⟩ := ih (j+1) (pre++Streaming.marks (binary w d)) (advance rows x d)
      (by simp only [List.length_cons] at hj; omega) hnext
      (by exact hx) rfl rfl rfl (fun a ha=>hd a (List.mem_cons_of_mem d ha))
    simp only [List.length_append,Streaming.marks_length,binary_length] at htail
    rw [show j+1+1=j+2 by omega] at htail
    have hwhole := hstep.trans htail
    refine ⟨r.steps+2+time,?_,?_⟩
    · simp only [List.length_cons]
      nlinarith
    · have hpos : pre.length+2*w+(RowTupleFilterLoop.word w ds).length=
          pre.length+(RowTupleFilterLoop.word w (d::ds)).length := by
        simp only [RowTupleFilterLoop.word,List.flatMap_cons,List.length_append,Streaming.marks_length,binary_length]
        omega
      simpa only [machine,cfg,fold,hpos] using hwhole

theorem fold_output (rows : List (List Bool)) (ds : List ℕ) (x : Data) :
    (fold rows x ds).out=x.out++word rows ds ∧ (fold rows x ds).count=x.count+count rows ds := by
  induction ds generalizing x with
  | nil => simp [fold,word,count]
  | cons d ds ih =>
    obtain ⟨ho,hc⟩ := ih (advance rows x d)
    constructor
    · simpa [fold,word,advance,RowMaskLookupReusable.result,List.append_assoc] using ho
    · simpa [fold,count,advance,RowMaskLookupReusable.result,Nat.add_assoc] using hc

theorem tuple_run (N w M : ℕ) (rows : List (List Bool)) (ds : List ℕ) (tail : List Bool) (x : Data)
    (hx : x.source=rows.flatten) (hp : x.pos=0) (hi : x.index=0) (hc : x.counter=0)
    (hl : ∀ row∈rows,row.length=N) (hd : ∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M) :
    ∃ r,runFrom machine (budget N w M ds.length)
      (cfg 0 N w M ds.length 1 (RowTupleFilterLoop.word w ds++tail) 0 x)=some r ∧
      r.final=cfg 3 N w M ds.length 1 (RowTupleFilterLoop.word w ds++tail) (2*w*ds.length)
        (fold rows x ds) ∧ r.steps≤budget N w M ds.length := by
  obtain ⟨time,hbound,ht⟩ := remaining N w M ds.length 0 rows ds
    (RowTupleFilterLoop.word w ds++tail) [] tail x (by simp) (by simp) hx hp hi hc hl hd hb hM
  have hbudget : time≤budget N w M ds.length := by unfold budget; nlinarith
  simp only [List.length_nil,Nat.zero_add,RowTupleFilterLoop.word_length] at ht
  obtain ⟨r,hr,rf,rs⟩ := ht.run
    (by simp [machine,cfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
  have hmore := runFrom_moreFuel machine time (budget N w M ds.length-time) _ r hr
  rw [Nat.add_sub_of_le hbudget] at hmore
  exact ⟨r,hmore,rf,rs.le.trans hbudget⟩

end NearCubicWires.RepairOrdinary.RowTupleMaskLoop
