import Proof.Amplification.RecoveryCanonicalVerifier
import Proof.Amplification.RecoveryVerifierBound

/-! Abstract canonical completeness packaging before specializing the
large fixed verifier. Its exact original input and paid run are retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryVerifierCarrier
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem accepts_complete {t s : Nat} (p : Machine t s) (accept : Fin s→Bool) (ht : 2 ≤ t)
    (input witness : List Bool) (source : Fin t→List Bool) (bound fuel : Nat)
    (hi : (verifier p accept ht).inputTapes input witness=source)
    (h : ∃ r,run p bound source=some r ∧ accept r.final.control=true)
    (hb : bound≤fuel) : (verifier p accept ht).acceptsAt fuel input witness := by
  obtain ⟨r,hr,ha⟩ := h
  have hm := run_moreFuel p bound (fuel-bound) source r hr
  rw [Nat.add_sub_of_le hb] at hm
  refine ⟨r,?_,ha⟩
  change run p fuel ((verifier p accept ht).inputTapes input witness)=some r
  rw [hi]
  exact hm

end NearCubicWires.RepairOrdinary.RecoveryVerifierCarrier
