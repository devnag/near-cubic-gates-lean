import Proof.CaseAnalysis.RowsSignedAppend

/-! Exact sign acceptance for the existing canonical integer codec.
The three binary comparisons also reject negative zero. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerMeaning
open RadixSemantics CanonicalBinary CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def magnitude (bits : List Bool):=value (BitFields.payload (RecoveryFixedUnpair.rightWord bits))
def valid (bits : List Bool) : Prop:=
  (decodeNat (value (RecoveryFixedUnpair.rightWord bits))).isSome ∧
    (value (RecoveryFixedUnpair.leftWord bits)=0 ∨
      value (RecoveryFixedUnpair.leftWord bits)=1 ∧ magnitude bits≠0)

theorem valid_iff (bits : List Bool) : valid bits ↔ (decodeInt (value bits)).isSome:=by
  constructor
  · rintro ⟨hn,hs⟩
    have hp:BitFields.passes (RecoveryFixedUnpair.rightWord bits):=(BitFields.passes_iff _).mpr hn
    have hm:=encodeNat_of_decode (BitFields.decode_of_passes _ hp)
    change encodeNat (magnitude bits)=value (RecoveryFixedUnpair.rightWord bits) at hm
    have hpair:Nat.pair (value (RecoveryFixedUnpair.leftWord bits))
        (value (RecoveryFixedUnpair.rightWord bits))=value bits:=by
      rw [(RecoveryFixedUnpair.word_values bits).1,(RecoveryFixedUnpair.word_values bits).2,Nat.pair_unpair]
    rcases hs with hs|⟨hs,hpos⟩
    · have hc:encodeInt (magnitude bits : ℤ)=value bits:=by
        calc
          _=Nat.pair 0 (encodeNat (magnitude bits)):=by simp [encodeInt]
          _=Nat.pair (value (RecoveryFixedUnpair.leftWord bits))
              (value (RecoveryFixedUnpair.rightWord bits)):=by rw [hs,hm]
          _=value bits:=hpair
      rw [←hc,decodeInt_encode]
      rfl
    · have hc:encodeInt (-(magnitude bits : ℤ))=value bits:=by
        calc
          _=Nat.pair 1 (encodeNat (magnitude bits)):=by simp [encodeInt,hpos]
          _=Nat.pair (value (RecoveryFixedUnpair.leftWord bits))
              (value (RecoveryFixedUnpair.rightWord bits)):=by rw [hs,hm]
          _=value bits:=hpair
      rw [←hc,decodeInt_encode]
      rfl
  · intro h
    obtain ⟨z,hz⟩:=Option.isSome_iff_exists.mp h
    have hc:=encodeInt_of_decode hz
    have hm:value (RecoveryFixedUnpair.rightWord bits)=encodeNat z.natAbs:=by
      rw [(RecoveryFixedUnpair.word_values bits).2,←hc,encodeInt,Nat.unpair_pair]
    have hs:value (RecoveryFixedUnpair.leftWord bits)=if z<0 then 1 else 0:=by
      rw [(RecoveryFixedUnpair.word_values bits).1,←hc,encodeInt,Nat.unpair_pair]
    have hp:=BitFields.encoded_passes (RecoveryFixedUnpair.rightWord bits) z.natAbs hm
    have hv:magnitude bits=z.natAbs:=by
      rw [magnitude,hp.2,RecoveryUnpair.bits_value]
    refine ⟨by rw [hm,decodeNat_encode];rfl,?_⟩
    by_cases hn:z<0
    · right
      refine ⟨by simpa only [if_pos hn] using hs,?_⟩
      rw [hv]
      exact Int.natAbs_ne_zero.mpr (by omega)
    · left
      simpa only [if_neg hn] using hs

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerMeaning
