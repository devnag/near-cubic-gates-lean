import Proof.Amplification.RecoveryRawBranchCalls

/-! Exact raw/default dispatch after actual syntax validation. An invalid
Boolean tag retains the corrected decoder's accepted-empty default before
any raw index-bound gate; ordinary valid tags require that gate and SAT. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawBranch
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def evaluated (x : State) (word : List Bool) (k : Nat) :=
  RecoveryRawSATTable.answer x.view.width x.eval.valuation.cap 0 0 (total x word k) word x.eval.code
def answer (x : State) (word : List Bool) (k : Nat) :=
  RecoveryRawViewEntry.answer x.view word k &&
    if (output x word k).view.inner.tags then (output x word k).view.inner.bounded && evaluated x word k else true

theorem total_bound (x : State) (word : List Bool) (k : Nat)
    (ha : RecoveryRawViewEntry.answer x.view word k=true) : total x word k ≤ x.view.limit := by
  obtain ⟨n,rest,hp,_⟩ := RecoveryRawViewEntry.accepted_case x.view word k ha
  have hn := (RecoveryCertificateCount.readCount_some x.view.limit n (word.drop k) rest hp).1
  unfold total
  rw [RecoveryRawViewEntry.output_some x.view word k n rest hp]
  exact hn

theorem answer_sound (x : State) (word : List Bool) (k : Nat) (hx : x.view.Valid)
    (hs : x.view.inner.stream.source=frame word) (hp : x.view.inner.stream.pos=2*k)
    (hcode : RecoveryRawViewBody.code x.view=x.eval.code)
    (ht0 : x.view.inner.tags=true)
    (hb : RadixSemantics.value x.view.inner.bound=natBitLength x.eval.code)
    (ha : answer x word k=true) : correctedSat x.eval.code=true := by
  rw [answer,Bool.and_eq_true] at ha
  obtain ⟨view,hsyntax,htags,hbounded⟩ := RecoveryRawViewEntry.accepted_syntax x.view word k hx hs hp ha.1
  rw [hcode] at hsyntax
  rw [ht0,Bool.true_and] at htags
  cases ht : (output x word k).view.inner.tags
  · have hbad : RawSyntaxCertificate.tagsValid view=false := htags.symm.trans ht
    exact RawSyntaxCertificate.invalid_raw_accepted x.eval.code view hsyntax hbad
  · have htagsTrue : RawSyntaxCertificate.tagsValid view=true := htags.symm.trans ht
    have haccept := ha.2
    change (if (output x word k).view.inner.tags then (output x word k).view.inner.bounded && evaluated x word k else true)=true at haccept
    simp only [ht,ite_true,Bool.and_eq_true] at haccept
    have hindices : RecoveryRawViewLoop.boundedView (natBitLength x.eval.code) view=true := by
      have h := hbounded.symm.trans haccept.1
      rw [Bool.and_eq_true] at h
      rw [←hb]
      exact h.2
    exact RecoveryRawSATTable.guarded_answer_sound x.view.width x.eval.valuation.cap (total x word k)
      x.eval.code word view hsyntax htagsTrue hindices haccept.2

end NearCubicWires.RepairOrdinary.RecoveryRawBranch
