import Proof.Amplification.RecoveryVerifierCarrier

/-! The literal ordinary verifier ABI and all-witness, all-fuel soundness.
Its input is binary code.bits and the original witness; all491 remaining
tapes start blank. Bounded canonical completeness is the remaining NP gate. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdVerifier
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def inputShape (n : Nat) (bits word : List Bool) (i : Fin n) : List Bool :=
  if i.val=0 then frame bits else if i.val=1 then frame word else []

theorem extend_input (m n : Nat) (hm : 2 ≤ m) (bits word : List Bool) :
    Fin.addCases (m:=m) (n:=n) (motive:=fun _=>List Bool)
      (inputShape m bits word) (fun _=>[])=inputShape (m+n) bits word := by
  funext i
  refine Fin.addCases (m:=m) (n:=n) ?_ ?_ i
  · intro j
    simp only [Fin.addCases_left,inputShape,Fin.val_castAdd]
    rfl
  · intro j
    simp only [Fin.addCases_right,inputShape,Fin.val_natAdd]
    rw [if_neg (by omega),if_neg (by omega)]

theorem input_eq (bits word : List Bool) :
    RecoveryColdCompact.input bits word=inputShape 493 bits word := by
  have h4 : RecoveryColdFront.input bits word=inputShape 279 bits word :=
    RecoveryColdFront.input_layout bits word
  have h5 : RecoveryColdMarker.input bits word=inputShape 338 bits word := by
    unfold RecoveryColdMarker.input RecoveryColdMarker.lift
    rw [h4]
    exact extend_input 279 59 (by decide) bits word
  unfold RecoveryColdCompact.input RecoveryColdCompact.bankInput
  rw [h5]
  exact extend_input 338 155 (by decide) bits word

noncomputable def verifier : Verifier :=
  RecoveryVerifierCarrier.verifier machine accepting (by decide)

theorem verifier_input (bits word : List Bool) :
    verifier.inputTapes bits word=RecoveryColdCompact.input bits word :=
  (input_eq bits word).symm

theorem accepts_sound (code : Nat) (word : List Bool) (fuel : Nat)
    (ha : verifier.acceptsAt fuel code.bits word) : correctedSat code=true :=
  RecoveryVerifierCarrier.accepts_sound machine accepting (by decide) code.bits word
    (RecoveryColdCompact.input code.bits word) (budget code.bits word) (correctedSat code=true)
    (verifier_input code.bits word) (cold_run code word) fuel ha

end NearCubicWires.RepairOrdinary.RecoveryColdVerifier
