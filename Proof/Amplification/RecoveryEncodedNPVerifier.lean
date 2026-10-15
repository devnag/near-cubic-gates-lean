import Proof.Amplification.RecoveryVerifierCompletenessCarrier

/-! Literal local NP realization of correctedSat on every numeric code.
The fixed493-tape verifier starts with only binary code and witness inputs.
All-code soundness and bounded canonical completeness use this same machine. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdVerifier
open LocalBitMultitape
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem canonical_accepts (code : Nat) (c : Certificate) (hc : Fits code c)
    (hsel : selected c=c) (hcheck : check code c=true) :
    verifier.acceptsAt (8796093022208*(natBitLength code+1)^4)
      code.bits (RecoveryColdCanonical.witness code c) :=
  RecoveryVerifierCarrier.accepts_complete machine accepting (by decide)
    code.bits (RecoveryColdCanonical.witness code c)
    (RecoveryColdCompact.input code.bits (RecoveryColdCanonical.witness code c))
    (budget code.bits (RecoveryColdCanonical.witness code c)) (8796093022208*(natBitLength code+1)^4)
    (verifier_input code.bits (RecoveryColdCanonical.witness code c))
    (RecoveryColdCanonical.verifier_accept code c hc hsel hcheck)
    (bounded_witness_budget code _ (TableFirst.pack_bound code c hc))

noncomputable def encodedNPVerifier : RepairSource.EncodedNPVerifier correctedSat where
  verifier := verifier
  coefficient := 8796093022208
  coefficientPositive := by decide
  degree := 4
  correct := by
    intro code
    constructor
    · intro hs
      obtain ⟨c,hcheck,hfit,hselected⟩ := (bounded_selected_certificate code).mp hs
      refine ⟨RecoveryColdCanonical.witness code c,?_,canonical_accepts code c hfit hselected hcheck⟩
      have hw := TableFirst.pack_bound code c hfit
      have hp : (natBitLength code+1)^3≤(natBitLength code+1)^4 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      change (TableFirst.pack (Serialization.width code) c).length≤8796093022208*(natBitLength code+1)^4
      omega
    · rintro ⟨word,_,ha⟩
      exact accepts_sound code word (8796093022208*(natBitLength code+1)^4) ha

end NearCubicWires.RepairOrdinary.RecoveryColdVerifier
