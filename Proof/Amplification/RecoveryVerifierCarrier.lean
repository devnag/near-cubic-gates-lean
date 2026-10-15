import Proof.Amplification.RecoveryVerifier

/-! Abstract ordinary-verifier packaging. Deterministic all-fuel soundness
is proved before instantiating the large fixed cold controller. -/
namespace NearCubicWires.RepairOrdinary.RecoveryVerifierCarrier
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def verifier {t s : Nat} (p : Machine t s) (accept : Fin s→Bool) (ht : 2 ≤ t) : Verifier where
  tapeCount := t
  stateCount := s
  twoTapes := ht
  machine := p
  accepting := accept

theorem accepts_sound {t s : Nat} (p : Machine t s) (accept : Fin s→Bool) (ht : 2 ≤ t)
    (input witness : List Bool) (source : Fin t→List Bool) (bound : Nat) (P : Prop)
    (hi : (verifier p accept ht).inputTapes input witness=source)
    (h : ∃ r,run p bound source=some r ∧ r.steps≤bound ∧ (accept r.final.control=true → P))
    (fuel : Nat) (ha : (verifier p accept ht).acceptsAt fuel input witness) : P := by
  obtain ⟨actual,hactual,haccept⟩ := ha
  rw [hi] at hactual
  obtain ⟨checked,hchecked,_,hsound⟩ := h
  have hc := run_moreFuel p bound fuel _ checked hchecked
  have ha := run_moreFuel p fuel bound _ actual hactual
  rw [Nat.add_comm fuel bound] at ha
  have he : actual=checked := Option.some.inj (ha.symm.trans hc)
  apply hsound
  rw [←he]
  exact haccept

end NearCubicWires.RepairOrdinary.RecoveryVerifierCarrier
