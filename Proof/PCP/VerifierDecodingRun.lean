import Proof.PCP.VerifierDecoding

/-! The exact semantic execution dock: the decoder changes only the unused
descriptionBits annotation. Every run, cost receipt and acceptance bit agrees. -/
namespace NearCubicWires.RepairSource.VerifierDecoding
open LocalBitMultitape VerifierEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem canonical_runFrom (v : OrdinaryVerifier) (fuel : ℕ)
    (config : Configuration v.tapeCount v.stateCount) :
    runFrom (canonical v).machine fuel config = runFrom v.machine fuel config := by
  induction fuel generalizing config with
  | zero => rfl
  | succ fuel ih =>
    simp only [canonical] at ih
    simp only [runFrom, canonical, step, ih]

theorem canonical_run (v : OrdinaryVerifier) (fuel : ℕ)
    (input : Fin v.tapeCount → List Bool) :
    run (canonical v).machine fuel input = run v.machine fuel input :=
  canonical_runFrom v fuel _

theorem canonical_acceptsAt (v : OrdinaryVerifier) (fuel : ℕ)
    (input witness : List Bool) :
    (canonical v).acceptsAt fuel input witness ↔ v.acceptsAt fuel input witness := by
  change (∃ receipt, run (canonical v).machine fuel (v.inputTapes input witness) = some receipt ∧
    v.accepting receipt.final.control = true) ↔ _
  rw [canonical_run]
  rfl

theorem decoder_acceptance (v : OrdinaryVerifier) (N : ℕ)
    (hc : (code v).length ≤ Nat.log 2 N) (fuel : ℕ) (input witness : List Bool) :
    ∃ decoded, decode N (code v) = some decoded ∧
      (decoded.acceptsAt fuel input witness ↔ v.acceptsAt fuel input witness) :=
  ⟨canonical v, decode_code v N hc, canonical_acceptsAt v fuel input witness⟩

end NearCubicWires.RepairSource.VerifierDecoding
