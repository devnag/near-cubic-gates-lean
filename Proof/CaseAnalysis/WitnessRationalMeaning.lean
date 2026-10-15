import Proof.CaseAnalysis.WitnessRational

/-! Exact all-raw meaning of the already executed coefficient fields.
Canonical integer and natural guards followed by positive denominator and
gcd-one tests are equivalent to the unchanged canonical rational decoder. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.RationalCold
open LocalBitMultitape RadixSemantics CanonicalBinary CanonicalWitnessCodec
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def valid (bits : List Bool) : Prop:=PairHeader.valid bits ∧
  (decodeInt (value (numeratorWord bits))).isSome ∧
  (decodeNat (value (denominatorWord bits))).isSome ∧
  value (denominator bits)≠0 ∧ (value (numerator bits)).gcd (value (denominator bits))=1

theorem numerator_value (bits : List Bool) (z : ℤ)
    (hz : decodeInt (value (numeratorWord bits))=some z) : value (numerator bits)=z.natAbs:=by
  have hc:=encodeInt_of_decode hz
  have hm:value (RecoveryFixedUnpair.rightWord (numeratorWord bits))=encodeNat z.natAbs:=by
    rw [(RecoveryFixedUnpair.word_values (numeratorWord bits)).2,←hc,encodeInt,Nat.unpair_pair]
  have hp:=BitFields.encoded_passes _ _ hm
  change value (BitFields.payload (RecoveryFixedUnpair.rightWord (numeratorWord bits)))=z.natAbs
  rw [hp.2,RecoveryUnpair.bits_value]
theorem denominator_value (bits : List Bool) (d : ℕ)
    (hd : decodeNat (value (denominatorWord bits))=some d) : value (denominator bits)=d:=by
  have hp:=BitFields.encoded_passes _ _ (encodeNat_of_decode hd).symm
  change value (BitFields.payload (denominatorWord bits))=d
  rw [hp.2,RecoveryUnpair.bits_value]

theorem decoded_words (bits : List Bool) (q : ℚ)
    (hd : decodeCanonicalRational (value bits)=some q) :
    PairHeader.valid bits ∧ decodeInt (value (numeratorWord bits))=some q.num ∧
      decodeNat (value (denominatorWord bits))=some q.den:=by
  have he: value bits=encodeTaggedList [encodeInt q.num,encodeNat q.den]:=
    (encodeCanonicalRational_of_decode hd).symm
  have hv:=PairHeader.extracted_values bits _ _ he
  have hn:value (numeratorWord bits)=encodeInt q.num:=hv.2.1
  have hden:value (denominatorWord bits)=encodeNat q.den:=hv.2.2
  exact ⟨hv.1,by rw [hn,decodeInt_encode],by rw [hden,decodeNat_encode]⟩

theorem valid_iff (bits : List Bool) : valid bits ↔
    ∃ q,decodeCanonicalRational (value bits)=some q:=by
  constructor
  · rintro ⟨hh,hz,hd,hpos,hg⟩
    obtain ⟨z,hz⟩:=Option.isSome_iff_exists.mp hz
    obtain ⟨d,hd⟩:=Option.isSome_iff_exists.mp hd
    have hc:value bits=RationalFields.code z d:=by
      have hp:=(PairHeader.valid_iff bits).mp hh
      change value bits=encodeTaggedList [value (numeratorWord bits),value (denominatorWord bits)] at hp
      rw [←encodeInt_of_decode hz,←encodeNat_of_decode hd] at hp
      exact hp
    rw [numerator_value bits z hz,denominator_value bits d hd] at hg
    rw [denominator_value bits d hd] at hpos
    rw [hc]
    exact (RationalFields.decode_code_iff z d).mpr ⟨hpos,hg⟩
  · rintro ⟨q,hq⟩
    obtain ⟨hh,hn,hd⟩:=decoded_words bits q hq
    refine ⟨hh,by rw [hn];rfl,by rw [hd];rfl,?_,?_⟩
    · rw [denominator_value bits q.den hd]
      exact q.den_nz
    · rw [numerator_value bits q.num hn,denominator_value bits q.den hd]
      exact q.reduced.gcd_eq_one

theorem guarded_iff (bits : List Bool) (cap : ℕ) :
    (valid bits ∧ natBitLength (value (numerator bits)) ≤ cap ∧
      natBitLength (value (denominator bits)) ≤ cap) ↔
    ∃ q,decodeCanonicalRational (value bits)=some q ∧
      natBitLength q.num.natAbs ≤ cap ∧ natBitLength q.den ≤ cap:=by
  constructor
  · rintro ⟨hv,hn,hd⟩
    obtain ⟨q,hq⟩:=(valid_iff bits).mp hv
    obtain ⟨_,hnum,hden⟩:=decoded_words bits q hq
    exact ⟨q,hq,by simpa only [numerator_value bits q.num hnum] using hn,
      by simpa only [denominator_value bits q.den hden] using hd⟩
  · rintro ⟨q,hq,hn,hd⟩
    obtain ⟨_,hnum,hden⟩:=decoded_words bits q hq
    exact ⟨(valid_iff bits).mpr ⟨q,hq⟩,
      by simpa only [numerator_value bits q.num hnum] using hn,
      by simpa only [denominator_value bits q.den hden] using hd⟩

theorem code_length (bits : List Bool) (i : Fin 2) : (PairHeader.codeWord bits i).length=bits.length:=by
  simp only [PairHeader.codeWord,(RecoveryFixedUnpair.word_lengths _).1,CompetitorWitnessTriple.word_length]
theorem payload_lengths (bits : List Bool) :
    (numerator bits).length ≤ bits.length+1 ∧ (denominator bits).length ≤ bits.length+1:=by
  have hn:=CloseoutRowsIntegerGuard.payload_bound (numeratorWord bits)
  have hd:=Reencode.count_bound (denominatorWord bits)
  refine ⟨?_,?_⟩
  · simpa only [numerator,numeratorWord,code_length] using hn
  · simpa only [denominator,BitFields.payload,Reencode.fields,List.length_map,
      TraversalCounted.count,denominatorWord,code_length] using hd

end NearCubicWires.RepairOrdinary.CloseoutWitness.RationalCold
