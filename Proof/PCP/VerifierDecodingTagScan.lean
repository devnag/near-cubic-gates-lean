import Proof.PCP.VerifierDecodingTag
import Proof.PCP.VerifierDecodingRepeat

/-! Enclosing repeated scans for state flags and action tags. The retained
source is the literal code; the semantic suffix only describes the bytes
actually consumed by the checked finite reader. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.TagScan
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State where
  source : List Bool
  pos : ℕ
  rest : List Bool

def Inv (x : State) : Prop := ∃ pre, x.source = pre++frame x.rest ∧ x.pos = pre.length
noncomputable def input (x : State) := TagMachine.cfg 0 (fun _ => false) x.source x.pos

def next (limit : Fin 5) (test : TagMachine.Word → Bool) (x : State) : Bool × State :=
  (if limit.val ≤ x.rest.length then test (TagMachine.received (TagMachine.extend x.rest) limit.val) else false,
   ⟨x.source,x.pos+(if limit.val ≤ x.rest.length then 2*limit.val else 2*x.rest.length+1),x.rest.drop limit.val⟩)
noncomputable def accepted (limit : Fin 5) (test : TagMachine.Word → Bool)
    (q : Fin (Fintype.card TagMachine.Control)) (_ : Fin 1 → Bool) : Bool :=
  match TagMachine.code.symm q with
  | none => false
  | some (phase,bits) => decide (phase.val = 2*limit.val) && test bits
noncomputable def machine (limit : Fin 5) (test : TagMachine.Word → Bool) :=
  RepeatMachine.machine (TagMachine.machine limit) (accepted limit test)

theorem next_inv (limit : Fin 5) (test : TagMachine.Word → Bool) (x : State)
    (hx : Inv x) (h : (next limit test x).1 = true) : Inv (next limit test x).2 := by
  obtain ⟨pre,hsource,hpos⟩ := hx
  have hfull : limit.val ≤ x.rest.length := by
    by_contra hn
    simp [next,hn] at h
  refine ⟨pre++Streaming.marks (x.rest.take limit.val),?_,?_⟩
  · simp only [next]
    rw [List.append_assoc,←Streaming.frame_append,List.take_append_drop]
    exact hsource
  · simp [next,hfull,hpos,Streaming.marks_length]

theorem supplier (limit : Fin 5) (test : TagMachine.Word → Bool) (x : State) (hx : Inv x) :
    ∃ r, runFrom (TagMachine.machine limit) (2*limit.val+1) (input x) = some r ∧ r.steps ≤ 2*limit.val+1 ∧
      r.final.heads = (input (next limit test x).2).heads ∧
      r.final.tapes = (input (next limit test x).2).tapes ∧
      accepted limit test r.final.control r.final.scanned = (next limit test x).1 ∧
      ((next limit test x).1 = true → Inv (next limit test x).2) := by
  obtain ⟨pre,hsource,hpos⟩ := hx
  obtain ⟨r,hr,hs,hf⟩ := TagMachine.bounded_run pre x.rest limit
  have hi : TagMachine.cfg 0 (fun _ => false) (pre++frame x.rest) pre.length = input x := by
    simp only [input,hsource,hpos]
  rw [hi] at hr
  refine ⟨r,hr,hs,?_,?_,?_,next_inv limit test x ⟨pre,hsource,hpos⟩⟩
  all_goals
    by_cases h : limit.val ≤ x.rest.length
    · simp only [TagMachine.Result,if_pos h] at hf
      simp [hf,TagMachine.cfg,input,next,h,accepted,hsource,hpos]
    · simp only [TagMachine.Result,if_neg h] at hf
      simp [hf,TagMachine.rejected,input,TagMachine.cfg,next,h,accepted,hsource,hpos,Nat.add_assoc]

/-- Complete repeated constant-field validation. Both body and driver are
actual finite machines, and all malformed suffixes stop within this bound. -/
theorem scan_run (pre bits : List Bool) (count : ℕ) (limit : Fin 5) (test : TagMachine.Word → Bool) :
    let x : State := ⟨pre++frame bits,pre.length,bits⟩
    ∃ receipt,
      runFrom (machine limit test) (count*(2*limit.val+4)+3)
        (RepeatMachine.cfg 0 (input x) count 1) = some receipt ∧
      receipt.steps ≤ count*(2*limit.val+4)+3 ∧
      RepeatMachine.Result input count (RepeatMachine.iterate (next limit test) count x) receipt.final := by
  exact RepeatMachine.repeat_run (TagMachine.machine limit) (accepted limit test) input (next limit test) Inv
    (2*limit.val+1) (by intro x hx; rfl) (supplier limit test) count _ ⟨pre,rfl,rfl⟩

end NearCubicWires.RepairSource.VerifierDecoding.TagScan
