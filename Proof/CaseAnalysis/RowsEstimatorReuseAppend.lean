import Proof.CaseAnalysis.RowsEstimatorReuseLayout

/-! Append the estimator's actual padded record in its reusable ambient
bank. The copy changes only the growing scalar stream and its cursor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
open LocalBitMultitape CloseoutRowsEstimatorCoefficients
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def append (p : Program):=RecoveryFocus.machine (copySlots p) AppendCopy.machine

theorem append_run (p : Program) (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator D : ℕ)
    (out : List Bool) (H : Fin (tapes p)→ℕ) (A : Fin (tapes p)→List Bool)
    (hD:20*b+27≤D+1)
    (hrecord:A (old p (Whole.recordSlot p))=ZeroPadding.pad D (Stream.recordWord b q count denominator))
    (hout:A (output p)=out) (hlog:A (log p)=List.replicate (D+1) false)
    (hrhead:H (old p (Whole.recordSlot p))=0) (hohead:H (output p)=out.length) (hlhead:H (log p)=0) :
    ∃ r,runFrom (append p) (40*b+56) ⟨(append p).start,H,A⟩=some r ∧
      r.steps≤40*b+56 ∧
      r.final.heads=Function.update H (output p) (out++Stream.recordWord b q count denominator).length ∧
      r.final.tapes=Function.update A (output p) (out++Stream.recordWord b q count denominator):=by
  obtain ⟨base,hb,bh,bt,bs⟩:=AppendPadded.run b q count denominator D (D+1) out hD
  obtain ⟨r,rr,_,rs,rh,rt,keep⟩:=RecoveryFocus.dock (copySlots p) (copy_injective p)
    AppendCopy.machine (40*b+56) H A _
    (by intro j;fin_cases j;exact hrhead;exact hohead;exact hlhead)
    (by intro j;fin_cases j;exact hrecord;exact hout;exact hlog) base hb
  have distinct (j : Fin 3) (hj:j≠1):copySlots p j≠output p:=by
    intro he
    exact hj (copy_injective p he)
  refine ⟨r,rr,rs.trans_le bs,?_,?_⟩
  · funext i
    by_cases hi:∃ j,copySlots p j=i
    · obtain ⟨j,rfl⟩:=hi
      have h:=rh j
      rw [bh] at h
      fin_cases j
      · exact h.trans (hrhead.symm.trans (Function.update_of_ne (distinct 0 (by decide)) _ _).symm)
      · exact h.trans (Function.update_self (output p) (out++Stream.recordWord b q count denominator).length H).symm
      · exact h.trans (hlhead.symm.trans (Function.update_of_ne (distinct 2 (by decide)) _ _).symm)
    · have hn:∀ j,copySlots p j≠i:=by simpa only [not_exists] using hi
      have ho:i≠output p:=fun he=>hi ⟨1,he.symm⟩
      exact (keep i hn).1.trans (Function.update_of_ne ho _ _).symm
  · funext i
    by_cases hi:∃ j,copySlots p j=i
    · obtain ⟨j,rfl⟩:=hi
      have h:=rt j
      rw [bt] at h
      fin_cases j
      · exact h.trans (hrecord.symm.trans (Function.update_of_ne (distinct 0 (by decide)) _ _).symm)
      · exact h.trans (Function.update_self (output p) (out++Stream.recordWord b q count denominator) A).symm
      · exact h.trans (hlog.symm.trans (Function.update_of_ne (distinct 2 (by decide)) _ _).symm)
    · have hn:∀ j,copySlots p j≠i:=by simpa only [not_exists] using hi
      have ho:i≠output p:=fun he=>hi ⟨1,he.symm⟩
      exact (keep i hn).2.trans (Function.update_of_ne ho _ _).symm

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
