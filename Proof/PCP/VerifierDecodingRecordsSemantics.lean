import Proof.PCP.VerifierDecodingRecords

/-! Exact logical result and consumed length of the executed record loop.
The final delimiter will establish full length equality from this cursor. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.RecordsMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tests (bound : List Bool) (t : ℕ) : ℕ → List Bool → Bool
  | 0,_ => true
  | e+1,bits => RecordMachine.recordValid bits bound t && tests bound t e (bits.drop (width bound t))

theorem iterate_tests (bound : List Bool) (t e : ℕ) (x : State) :
    (RepeatMachine.iterate (next bound t) e x).1=tests bound t e x.bits := by
  induction e generalizing x with
  | zero => rfl
  | succ e ih =>
    cases h : RecordMachine.recordValid x.bits bound t <;>
      simp [RepeatMachine.iterate,next,tests,h,ih]

theorem next_source (bound : List Bool) (t : ℕ) (x : State) :
    (next bound t x).2.pre++frame (next bound t x).2.bits=x.pre++frame x.bits := by
  simp only [next]
  rw [List.append_assoc,←Streaming.frame_append,List.take_append_drop]

theorem next_pos (bound : List Bool) (t : ℕ) (x : State)
    (h : (next bound t x).1=true) :
    (next bound t x).2.pre.length=x.pre.length+2*width bound t := by
  have hl := valid_length x.bits bound t h
  simp [next,Streaming.marks_length,Nat.min_eq_left hl]

theorem successful_shape (bound : List Bool) (t e : ℕ) (x : State)
    (hx : Inv bound x) (h : (RepeatMachine.iterate (next bound t) e x).1=true) :
    let out := (RepeatMachine.iterate (next bound t) e x).2
    out.pre++frame out.bits=x.pre++frame x.bits ∧
      out.pre.length=x.pre.length+2*width bound t*e ∧
      out.bits=x.bits.drop (width bound t*e) ∧
      width bound t*e≤x.bits.length ∧ Inv bound out := by
  induction e generalizing x with
  | zero => simp [RepeatMachine.iterate,hx]
  | succ e ih =>
    have hn : (next bound t x).1=true := by
      cases hn : (next bound t x).1 with
      | false => simp [RepeatMachine.iterate,hn] at h
      | true => rfl
    simp only [RepeatMachine.iterate,hn,↓reduceIte] at h ⊢
    have hnext : Inv bound (next bound t x).2 := backing_bound x.bits x.backing bound hx
    obtain ⟨hs,hp,hb,hl,hi⟩ := ih (next bound t x).2 hnext h
    have hfull := valid_length x.bits bound t hn
    refine ⟨hs.trans (next_source bound t x),?_,?_,?_,hi⟩
    · rw [hp,next_pos bound t x hn]
      ring
    · rw [hb]
      simp only [next,List.drop_drop]
      congr 1
      ring
    · simp only [next,List.length_drop] at hl
      have he : width bound t*(e+1)=width bound t+width bound t*e := by ring
      rw [he]
      omega

noncomputable def Checked (bound : List Bool) (t cap e : ℕ) (x : State)
    (final : Configuration 9 (Fintype.card (RepeatMachine.Control (Fintype.card (RecoveryCalls.Control RecordMachine.sizes))))) : Prop :=
  if tests bound t e x.bits then
    ∃ out : State, final=RepeatMachine.cfg 3 (input bound t cap out) e 1 ∧
      out.pre++frame out.bits=x.pre++frame x.bits ∧
      out.pre.length=x.pre.length+2*width bound t*e ∧
      out.bits=x.bits.drop (width bound t*e) ∧
      width bound t*e≤x.bits.length ∧ Inv bound out
  else final.control=RepeatMachine.phaseCode (Fintype.card (RecoveryCalls.Control RecordMachine.sizes)) 4

theorem checked_run (bound : List Bool) (t cap e : ℕ) (hc : 2*bound.length+1≤cap)
    (x : State) (hx : Inv bound x) :
    ∃ r, runFrom machine (e*(8*bound.length+12*t+33)+3)
        (RepeatMachine.cfg 0 (input bound t cap x) e 1)=some r ∧
      r.steps≤e*(8*bound.length+12*t+33)+3 ∧ Checked bound t cap e x r.final := by
  obtain ⟨r,hr,hs,hf⟩ := records_run bound t cap e hc x hx
  refine ⟨r,hr,hs,?_⟩
  have ht := iterate_tests bound t e x
  cases h : tests bound t e x.bits with
  | false => simpa only [Checked,h,Bool.false_eq_true,↓reduceIte,RepeatMachine.Result,ht] using hf
  | true =>
    have hshape := successful_shape bound t e x hx (ht.trans h)
    simp only [RepeatMachine.Result,ht,h,↓reduceIte] at hf
    simp only [Checked,h,↓reduceIte]
    exact ⟨_,hf,hshape⟩

end NearCubicWires.RepairSource.VerifierDecoding.RecordsMachine
