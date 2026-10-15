import Proof.Amplification.RecoveryCanonicalCall

/-! Positive complete execution of the literal493-tape accepting verifier
from the original binary code and chosen certificate word. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCanonical
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem body_accept (code : Nat) (c : Certificate) (hc : Fits code c) (hsel : selected c=c)
    (hcheck : check code c=true) :
    ∃ r,run RecoveryColdVerifier.body (RecoveryColdVerifier.bodyBudget code.bits (witness code c))
      (RecoveryColdCompact.input code.bits (witness code c))=some r ∧
      RecoveryColdVerifier.mask r.final.scanned=true := by
  obtain ⟨first,hfirst,hh,ht,hready⟩ := compact_run code c hc
  obtain ⟨last,hlast,hscan,hlh,hlt⟩ := checker_accept code c hc hsel hcheck first.final.heads first.final.tapes hready
  obtain ⟨r,hr,_,hrh,hrt⟩ := initial_accept RecoveryColdCompact.coldProgram RecoveryColdAllCode.checkerProgram 277
    (RecoveryColdCompact.coldBudget code.bits (witness code c)) (RecoveryColdAllCode.checkerBudget code.bits)
    _ first last hfirst hh ht hlast
  have hg : last.final.scanned 277=true := by
    change readTapeBit (last.final.tapes 277) (last.final.heads 277)=true
    rw [hlh,hlt,hh,ht]
    rfl
  have hs : r.final.scanned=last.final.scanned := by
    funext i
    change readTapeBit (r.final.tapes i) (r.final.heads i)=_
    rw [hrh,hrt]
    rfl
  refine ⟨r,hr,?_⟩
  simp only [RecoveryColdVerifier.mask,hs,hg,hscan,Bool.true_and]

theorem verifier_accept (code : Nat) (c : Certificate) (hc : Fits code c) (hsel : selected c=c)
    (hcheck : check code c=true) :
    ∃ r,run RecoveryColdVerifier.machine (RecoveryColdVerifier.budget code.bits (witness code c))
      (RecoveryColdCompact.input code.bits (witness code c))=some r ∧
      RecoveryColdVerifier.accepting r.final.control=true := by
  obtain ⟨first,hfirst,hpositive⟩ := body_accept code c hc hsel hcheck
  obtain ⟨r,hr,ha⟩ := RecoveryReturnScanned.finish_run RecoveryColdVerifier.body RecoveryColdVerifier.mask
    (RecoveryColdVerifier.bodyBudget code.bits (witness code c))
    (initialConfiguration RecoveryColdVerifier.body (RecoveryColdCompact.input code.bits (witness code c))) first hfirst
  exact ⟨r,hr,ha.trans hpositive⟩

end NearCubicWires.RepairOrdinary.RecoveryColdCanonical
