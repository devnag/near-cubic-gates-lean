import Proof.CaseAnalysis.RowsEstimatorAppendCopy

/-! The same fixed six-field copy consumes the record in a reused padded
bank. Its output remains literal and unpadded, at the global append cursor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.AppendPadded
open LocalBitMultitape CloseoutRowsEstimatorCoefficients
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def caps (D : ℕ) : Fin 3→ℕ:=![D,0,0]
def entry (source out : List Bool) (D L : ℕ) : Configuration 3 20:=
  ⟨AppendCopy.machine.start,![0,out.length,0],
    ![ZeroPadding.pad D source,out,List.replicate L false]⟩

theorem run (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator D L : ℕ) (out : List Bool)
    (hL:20*b+27≤L) :
    ∃ r,runFrom AppendCopy.machine (40*b+56)
      (entry (Stream.recordWord b q count denominator) out D L)=some r ∧
      r.final.heads=![0,(out++Stream.recordWord b q count denominator).length,0] ∧
      r.final.tapes=![ZeroPadding.pad D (Stream.recordWord b q count denominator),
        out++Stream.recordWord b q count denominator,List.replicate L false] ∧ r.steps≤40*b+56:=by
  obtain ⟨base,hb,bh,bt,bs⟩:=AppendCopy.run b q count denominator L out hL
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config AppendCopy.machine (caps D) _ _ base hb
  have hi:ZeroPadding.config (caps D)
      (AppendCopy.entry (Stream.recordWord b q count denominator) out L)=
      entry (Stream.recordWord b q count denominator) out D L:=by
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i
      · rfl
      · exact ZeroPadding.pad_zero _
      · exact ZeroPadding.pad_zero _
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,by omega⟩
  · rw [rf]
    exact bh
  · rw [rf]
    change (fun i=>ZeroPadding.pad (caps D i) (base.final.tapes i))=_
    rw [bt]
    funext i;fin_cases i
    · rfl
    · exact ZeroPadding.pad_zero _
    · exact ZeroPadding.pad_zero _

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.AppendPadded
