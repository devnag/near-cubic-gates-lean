import Proof.CaseAnalysis.WitnessRationalMeaning
import Proof.PCP.ProjectionDimensionCanonical

/-! Canonical payload length is the exact accepted bit policy, including
zero. This permits the physical width normalizer's early flag to guard the
unchanged gcd loop at the produced policy width. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.RationalCold
open RadixSemantics CanonicalBinary CanonicalWitnessCodec
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bits_length_iff (n b : ℕ) (hb : 1 ≤ b) : n.bits.length ≤ b ↔ natBitLength n ≤ b:=by
  by_cases hn:n=0
  · subst n
    change 0 ≤ b ↔ 1 ≤ b
    omega
  · rw [DimensionProducer.bits_length n (by omega)]

theorem denominator_length_iff (bits : List Bool) (d b : ℕ) (hb : 1 ≤ b)
    (hd : decodeNat (value (denominatorWord bits))=some d) :
    (denominator bits).length ≤ b ↔ natBitLength d ≤ b:=by
  have hp:=BitFields.encoded_passes _ _ (encodeNat_of_decode hd).symm
  change (BitFields.payload (denominatorWord bits)).length ≤ b ↔ _
  rw [hp.2]
  exact bits_length_iff d b hb
theorem numerator_length_iff (bits : List Bool) (z : ℤ) (b : ℕ) (hb : 1 ≤ b)
    (hz : decodeInt (value (numeratorWord bits))=some z) :
    (numerator bits).length ≤ b ↔ natBitLength z.natAbs ≤ b:=by
  have hc:=encodeInt_of_decode hz
  have hm:value (RecoveryFixedUnpair.rightWord (numeratorWord bits))=encodeNat z.natAbs:=by
    rw [(RecoveryFixedUnpair.word_values (numeratorWord bits)).2,←hc,encodeInt,Nat.unpair_pair]
  have hp:=BitFields.encoded_passes _ _ hm
  change (BitFields.payload (RecoveryFixedUnpair.rightWord (numeratorWord bits))).length ≤ b ↔ _
  rw [hp.2]
  exact bits_length_iff z.natAbs b hb

theorem length_guarded_iff (bits : List Bool) (b : ℕ) (hb : 1 ≤ b) :
    (valid bits ∧ (numerator bits).length ≤ b ∧ (denominator bits).length ≤ b) ↔
    ∃ q,decodeCanonicalRational (value bits)=some q ∧
      natBitLength q.num.natAbs ≤ b ∧ natBitLength q.den ≤ b:=by
  constructor
  · rintro ⟨hv,hn,hd⟩
    obtain ⟨q,hq⟩:=(valid_iff bits).mp hv
    obtain ⟨_,hnum,hden⟩:=decoded_words bits q hq
    exact ⟨q,hq,(numerator_length_iff bits q.num b hb hnum).mp hn,
      (denominator_length_iff bits q.den b hb hden).mp hd⟩
  · rintro ⟨q,hq,hn,hd⟩
    obtain ⟨_,hnum,hden⟩:=decoded_words bits q hq
    exact ⟨(valid_iff bits).mpr ⟨q,hq⟩,(numerator_length_iff bits q.num b hb hnum).mpr hn,
      (denominator_length_iff bits q.den b hb hden).mpr hd⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.RationalCold
