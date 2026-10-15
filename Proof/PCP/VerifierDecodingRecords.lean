import Proof.PCP.VerifierDecodingRecord

/-! The complete sequential record loop uses the actual record machine's
physical result bit. Its invariant is required only after accepted records;
the finite repeat controller immediately stops on malformed input. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.RecordsMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def width (bound : List Bool) (t : ℕ) : ℕ := 1+bound.length+4*t

theorem tag_length (bits : List Bool) (t : ℕ) (present : Bool)
    (h : TagScan.tests 4 (TagMachine.valid present) t bits=true) : 4*t≤bits.length := by
  let x : TagScan.State := ⟨[],0,bits⟩
  have hi := TagScan.iterate_tests 4 (TagMachine.valid present) t x
  have hs := TagScan.successful_shape 4 (TagMachine.valid present) t x (hi.trans h)
  exact hs.2.2.2

theorem valid_length (bits bound : List Bool) (t : ℕ)
    (h : RecordMachine.recordValid bits bound t=true) : width bound t≤bits.length := by
  cases bits with
  | nil => simp [RecordMachine.recordValid] at h
  | cons present bits =>
    cases present with
    | false =>
      simp only [RecordMachine.recordValid,Bool.false_eq_true,↓reduceIte,
        RecordMachine.absentValid,Bool.and_eq_true,decide_eq_true_eq] at h
      have ht := tag_length (bits.drop bound.length) t false h.2
      simp only [List.length_drop] at ht
      simp only [width,List.length_cons]
      omega
    | true =>
      simp only [RecordMachine.recordValid,↓reduceIte,
        RecordMachine.presentValid,Bool.and_eq_true,decide_eq_true_eq] at h
      have hj := h.1.1
      have ht := tag_length (bits.drop bound.length) t true h.2
      simp only [List.length_drop] at ht
      simp only [width,List.length_cons]
      omega

theorem backing_bound (bits backing bound : List Bool)
    (h : backing.length≤2*bound.length+1) :
    (RecordMachine.backingAfter bits backing bound).length≤2*bound.length+1 := by
  cases bits with
  | nil => exact h
  | cons present bits =>
    cases present with
    | false => exact h
    | true => simp [RecordMachine.backingAfter]

structure State where
  pre : List Bool
  bits : List Bool
  backing : List Bool
  rangeFlag : Bool
  result : Bool

def Inv (bound : List Bool) (x : State) : Prop := x.backing.length≤2*bound.length+1
noncomputable def input (bound : List Bool) (t cap : ℕ) (x : State) :=
  RecordMachine.cfg RecordMachine.machine.start (x.pre++frame x.bits) x.backing bound
    x.pre.length bound.length t cap x.rangeFlag x.result

def next (bound : List Bool) (t : ℕ) (x : State) : Bool × State :=
  (RecordMachine.recordValid x.bits bound t,
   ⟨x.pre++Streaming.marks (x.bits.take (width bound t)),x.bits.drop (width bound t),
    RecordMachine.backingAfter x.bits x.backing bound,x.bits.headD false,true⟩)

def accepted (_ : Fin (Fintype.card (RecoveryCalls.Control RecordMachine.sizes)))
    (bits : Fin 8 → Bool) : Bool := bits 7
noncomputable def machine := RepeatMachine.machine RecordMachine.machine accepted

theorem next_input (bound : List Bool) (t cap : ℕ) (x : State)
    (h : RecordMachine.recordValid x.bits bound t=true) :
    input bound t cap (next bound t x).2=
      RecordMachine.cfg RecordMachine.machine.start (x.pre++frame x.bits)
        (RecordMachine.backingAfter x.bits x.backing bound) bound
        (x.pre.length+2*(width bound t)) bound.length t cap (x.bits.headD false) true := by
  have hl := valid_length x.bits bound t h
  have hs : (x.pre++Streaming.marks (x.bits.take (width bound t)))++frame (x.bits.drop (width bound t))=
      x.pre++frame x.bits := by
    rw [List.append_assoc,←Streaming.frame_append,List.take_append_drop]
  simp only [input,next,hs,List.length_append,Streaming.marks_length,List.length_take,Nat.min_eq_left hl]

theorem supplier (bound : List Bool) (t cap : ℕ) (hc : 2*bound.length+1≤cap)
    (x : State) (hx : Inv bound x) :
    ∃ r, runFrom RecordMachine.machine (8*bound.length+12*t+30) (input bound t cap x)=some r ∧
      r.steps≤8*bound.length+12*t+30 ∧ accepted r.final.control r.final.scanned=(next bound t x).1 ∧
      ((next bound t x).1=true →
        r.final.heads=(input bound t cap (next bound t x).2).heads ∧
        r.final.tapes=(input bound t cap (next bound t x).2).tapes ∧ Inv bound (next bound t x).2) := by
  obtain ⟨r,hr,hs,hv,hf⟩ := RecordMachine.record_run x.pre x.bits x.backing bound t cap x.rangeFlag x.result hx hc
  refine ⟨r,hr,hs,hv,?_⟩
  intro h
  have he := next_input bound t cap x h
  rw [he,hf h]
  exact ⟨rfl,rfl,backing_bound x.bits x.backing bound hx⟩

/-- All record parsing, call returns, failure branches and the final driver
rewind are actual transitions. The supplied e-driver must start at head1. -/
theorem records_run (bound : List Bool) (t cap e : ℕ) (hc : 2*bound.length+1≤cap)
    (x : State) (hx : Inv bound x) :
    ∃ r, runFrom machine (e*(8*bound.length+12*t+33)+3)
        (RepeatMachine.cfg 0 (input bound t cap x) e 1)=some r ∧
      r.steps≤e*(8*bound.length+12*t+33)+3 ∧
      RepeatMachine.Result (input bound t cap) e (RepeatMachine.iterate (next bound t) e x) r.final := by
  exact RepeatMachine.rejecting_repeat_run RecordMachine.machine accepted (input bound t cap)
    (next bound t) (Inv bound) (8*bound.length+12*t+30)
    (by intro x hx; rfl) (supplier bound t cap hc) e x hx

end NearCubicWires.RepairSource.VerifierDecoding.RecordsMachine
