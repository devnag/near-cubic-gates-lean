import Proof.Amplification.RecoveryRawClauseShape

/-! The clause loop accumulates tag validity and raw variable bounds from
its certified natural-tag clause, retaining the same input-length bound. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawClause
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding RecoveryRawLiteralBound
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem out_flags (n : Nat) (x : State) (values : List (Nat×Nat))
    (hc : RawShape.clause n (code x)=some values) :
    (out n x).2.tags=(x.tags && values.all (fun literal=>decide (literal.1 ≤ 1))) ∧
      (out n x).2.bounded=(x.bounded && values.all (fun literal=>decide (literal.2 < RadixSemantics.value x.bound))) := by
  induction n generalizing x values with
  | zero=>
    cases he : code x with
    | zero=>
      have hv : values=[] := by simpa only [he,RawShape.clause,RawShape.codes,Option.map_some,List.map_nil,Option.some.injEq] using hc.symm
      subst values
      simp [out,RepeatMachine.iterate]
    | succ c=>simp [he,RawShape.clause,RawShape.codes] at hc
  | succ n ih=>
    have hn : code x≠0 := by intro hz; simp [hz,RawShape.clause,RawShape.codes] at hc
    rw [clause_step n (code x) hn] at hc
    cases ht : RawShape.clause n (Nat.unpair (code x-1)).2 with
    | none=>simp [ht] at hc
    | some tail=>
      have hv : head x::tail=values := by
        have h := hc
        simp only [ht,Option.map_some,Option.some.injEq] at h
        exact h
      subst values
      have hc' : RawShape.clause n (code (output x))=some tail := by rw [output_tail x hn]; exact ht
      obtain ⟨htags,hbounds⟩ := ih (output x) tail hc'
      rw [output_tags x hn] at htags
      rw [output_bounded x hn,output_bound] at hbounds
      rw [out_succ n x hn]
      constructor
      · simpa only [List.all_cons,Bool.and_assoc] using htags
      · simpa only [List.all_cons,Bool.and_assoc] using hbounds

theorem output_zero_flags (x : State) (hc : code x=0) :
    (output x).tags=x.tags ∧ (output x).bounded=x.bounded := by
  have hp : (decoded x).stream.data.present=false := by
    change (RecoveryRawLiteralStream.output x.stream).data.present=false
    rw [RecoveryRawLiteralStream.output_data,RecoveryRawLiteral.output_present]
    change decide (code x≠0)=false
    simp [hc]
  rw [output,if_neg (by rw [hp]; decide)]
  exact ⟨rfl,rfl⟩

theorem final_flags (n : Nat) (x : State) (values : List (Nat×Nat))
    (hc : RawShape.clause n (code x)=some values) :
    (inverted (output (out n x).2)).tags=(x.tags && values.all (fun literal=>decide (literal.1 ≤ 1))) ∧
      (inverted (output (out n x).2)).bounded=
        (x.bounded && values.all (fun literal=>decide (literal.2 < RadixSemantics.value x.bound))) := by
  have ha : answer n x=true := by rw [answer_shape,hc]; rfl
  have hz : code (out n x).2=0 := by
    rw [answer,Bool.and_eq_true,decide_eq_true_eq] at ha
    exact ha.2
  have hflags := output_zero_flags (out n x).2 hz
  change (output (out n x).2).tags=_ ∧ (output (out n x).2).bounded=_
  rw [hflags.1,hflags.2]
  exact out_flags n x values hc

end NearCubicWires.RepairOrdinary.RecoveryRawClause
