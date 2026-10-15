import Proof.Amplification.RecoveryRawViewBodyWhole

/-! Accepted raw-view bodies certify the actual outer head clause. Their
exact retained state supplies the next physical witness position. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewBody
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
open RepairSource.RecoveryOracle
open CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def code (x : State) := RadixSemantics.value x.outer.bits
def headCode (x : State) := (Nat.unpair (code x-1)).1

theorem prepared_code (x : State) (n : Nat) (hz : code x≠0) :
    RecoveryRawLiteralBound.code (prepared x n).inner=headCode x :=
  RecoveryCellStore.head_value x.outer.bits hz

theorem prepared_answer (x : State) (n : Nat) (hz : code x≠0) :
    clauseAnswer (prepared x n)=(RawShape.clause n (headCode x)).isSome := by
  change RecoveryRawClause.answer n (prepared x n).inner=_
  rw [RecoveryRawClause.answer_shape,prepared_code x n hz]

theorem accepted (x : State) (word : List Bool) (k : Nat) (ha : answer x word k=true) :
    code x≠0 ∧ ∃ n rest,readCount x.limit (word.drop k)=some (n,rest) ∧
      clauseAnswer (prepared x n)=true := by
  have hz : code x≠0 := by
    intro hz
    simp only [answer,show RadixSemantics.value x.outer.bits=0 from hz,ite_true,Bool.false_eq_true] at ha
  refine ⟨hz,?_⟩
  rw [answer,if_neg (show RadixSemantics.value x.outer.bits≠0 from hz)] at ha
  cases hp : readCount x.limit (word.drop k) with
  | none=>simp only [hp,Bool.false_eq_true] at ha
  | some pair=>
    rcases pair with ⟨n,rest⟩
    exact ⟨n,rest,rfl,by simpa only [hp] using ha⟩

theorem body_output_some (x : State) (word : List Bool) (k n : Nat) (rest : List Bool)
    (hp : readCount x.limit (word.drop k)=some (n,rest)) : bodyOutput x word k=output x n := by
  change (match readCount x.limit (word.drop k) with
    | none=>staged x | some (m,_)=>output x m)=_
  rw [hp]

theorem output_stable (x : State) (n : Nat) :
    (output x n).inner.bound=x.inner.bound ∧
      (output x n).inner.stream.source=x.inner.stream.source ∧ (output x n).limit=x.limit := by
  have h := RecoveryRawClause.final_stable n (prepared x n).inner
  exact ⟨h.1,h.2.2,rfl⟩

theorem output_tail (x : State) (n : Nat) (hz : code x≠0) :
    code (output x n)=(Nat.unpair (code x-1)).2 := by
  change RadixSemantics.value (x.outer.after 0).bits=_
  have h := RecoveryThreeCellReader.after_value x.outer 0 hz
  exact h

theorem output_pos (x : State) (hx : x.Valid) (n : Nat)
    (ha : clauseAnswer (prepared x n)=true) :
    (output x n).inner.stream.pos=x.inner.stream.pos+2*n+2+4*n*x.width := by
  have h := RecoveryRawClause.final_pos n (prepared x n).inner ha
  change (output x n).inner.stream.pos=(prepared x n).inner.stream.pos+4*n*(prepared x n).width at h
  rw [prepared_width x hx n] at h
  exact h

theorem output_flags (x : State) (n : Nat) (values : List (Nat×Nat))
    (hz : code x≠0) (hc : RawShape.clause n (headCode x)=some values) :
    (output x n).inner.tags=(x.inner.tags && values.all (fun literal=>decide (literal.1 ≤ 1))) ∧
      (output x n).inner.bounded=
        (x.inner.bounded && values.all (fun literal=>decide (literal.2 < RadixSemantics.value x.inner.bound))) := by
  have hc' : RawShape.clause n (RecoveryRawLiteralBound.code (prepared x n).inner)=some values := by
    rw [prepared_code x n hz]
    exact hc
  exact RecoveryRawClause.final_flags n (prepared x n).inner values hc'

theorem accepted_invariant (x : State) (word : List Bool) (k : Nat) (hx : x.Valid)
    (ha : answer x word k=true) :
    (bodyOutput x word k).Valid ∧ (bodyOutput x word k).width=x.width ∧
      (bodyOutput x word k).limit=x.limit ∧
      (bodyOutput x word k).inner.bound=x.inner.bound ∧
      (bodyOutput x word k).inner.stream.source=x.inner.stream.source := by
  obtain ⟨_,n,rest,hp,_⟩ := accepted x word k ha
  have hn := (RecoveryCertificateCount.readCount_some x.limit n (word.drop k) rest hp).1
  rw [body_output_some x word k n rest hp]
  have hstable := output_stable x n
  refine ⟨finished_valid _ (prepared_valid x hx n hn),?_,hstable.2.2,hstable.1,hstable.2.1⟩
  exact (finished_width _).trans (prepared_width x hx n)

end NearCubicWires.RepairOrdinary.RecoveryRawViewBody
