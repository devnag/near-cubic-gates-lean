import Proof.Amplification.RecoveryCanonicalRawAccept

/-! Every selected satisfying certificate has a positive run of the
literal all-code checker on its physically materialized canonical state. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCanonical
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem all_code_accept (code : Nat) (c : Certificate) (hc : Fits code c) (hsel : selected c=c)
    (hcheck : check code c=true) :
    ∃ r,runFrom RecoveryAllCode.machine (RecoveryAllCode.budget (RecoveryColdView.width code.bits))
      (RecoveryAllCode.cfg (canonicalState code c) RecoveryAllCode.machine.start)=some r ∧
      r.final.heads 93=0 ∧ r.final.tapes 93=[true] := by
  cases ht : RawSyntaxCertificate.tagsValid c.view with
  | false=>exact default_accept code c hc ht
  | true=>
    have hf : formulaCheck code (RawSyntaxCertificate.project c.view) c.table c.inner c.outer=true := by
      simpa only [check,hc.1,ht,Bool.true_and,ite_true] using hcheck
    by_cases hraw : wellSizedCNFEncoding code (RawSyntaxCertificate.project c.view)=true
    · have hs : FiniteValuation.check ⟨RawSyntaxCertificate.project c.view,0,0⟩ c.table=true := by
        simpa only [formulaCheck,hraw,ite_true] using hf
      exact raw_accept code c hc ht hraw hs
    · have hm : markerCheck (RawSyntaxCertificate.project c.view) c.table c.inner c.outer=true := by
        simpa only [formulaCheck,if_neg hraw] using hf
      exact compact_accept code c hc hsel ht hm

end NearCubicWires.RepairOrdinary.RecoveryColdCanonical
