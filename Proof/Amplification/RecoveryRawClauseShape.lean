import Proof.Amplification.RecoveryRawClauseWhole

/-! The physical clause answer is exactly the shape-guided decoder's
success, with no comparison against unused witness literal values. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawClause
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding RecoveryRawLiteralBound
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem clause_step (n c : Nat) (hc : c≠0) :
    RawShape.clause (n+1) c=(RawShape.clause n (Nat.unpair (c-1)).2).map
      (Nat.unpair (Nat.unpair (c-1)).1 :: ·) := by
  cases c with
  | zero=>contradiction
  | succ c=>
    unfold RawShape.clause
    rw [RawShape.codes,Nat.add_sub_cancel]
    cases RawShape.codes n (Nat.unpair c).2 <;> rfl

theorem out_succ (n : Nat) (x : State) (hc : code x≠0) :
    out (n+1) x=out n (output x) := by
  have hp : decide (code x≠0)=true := decide_eq_true hc
  simp only [out,RepeatMachine.iterate,RecoveryRawLiteralLoop.next,hp,ite_true]

theorem answer_shape (n : Nat) (x : State) :
    answer n x=(RawShape.clause n (code x)).isSome := by
  induction n generalizing x with
  | zero=>
    change decide (code x=0)=(RawShape.clause 0 (code x)).isSome
    cases hc : code x <;> simp [RawShape.clause,RawShape.codes]
  | succ n ih=>
    by_cases hc : code x=0
    · simp [answer,out,RepeatMachine.iterate,RecoveryRawLiteralLoop.next,hc,RawShape.clause,RawShape.codes]
    · have ha : answer (n+1) x=answer n (output x) := by
        unfold answer
        rw [out_succ n x hc]
      rw [ha,ih,clause_step n (code x) hc,output_tail x hc]
      cases RawShape.clause n (Nat.unpair (code x-1)).2 <;> rfl

theorem accepted_shape (n : Nat) (x : State) (h : answer n x=true) :
    ∃ values,RawShape.clause n (code x)=some values ∧ Encodable.encode values=code x := by
  rw [answer_shape] at h
  cases hs : RawShape.clause n (code x) with
  | none=>simp [hs] at h
  | some values=>exact ⟨values,rfl,RawShape.clause_sound n (code x) values hs⟩

theorem canonical_answer (x : State) (values : List (Nat×Nat))
    (hc : code x=Encodable.encode values) : answer values.length x=true := by
  rw [answer_shape,hc,RawShape.clause_complete]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryRawClause
