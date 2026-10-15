import Proof.CaseAnalysis.WitnessSelectedSource
import Proof.MachineModel.CanonicalRationalValidationProgram

/-! Exact semantic criterion for the executed coefficient field guards.
The old validated gcd characterization eliminates a second rational serializer;
all physical work remains the cold field readers and early-guarded gcd. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.RationalFields
open CanonicalBinary CanonicalWitnessCodec CanonicalRationalValidationProgram
open CanonicalTaggedTupleProgram CanonicalNatValidationProgram
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def code (numerator : ℤ) (denominator : ℕ):=encodeTaggedList [encodeInt numerator,encodeNat denominator]

theorem code_accepts (numerator : ℤ) (denominator : ℕ) :
    rationalValidationAccepts (code numerator denominator) ↔
      denominator≠0 ∧ numerator.natAbs.gcd denominator=1:=by
  have htuple:rationalTupleOutput (code numerator denominator)=
      Nat.pair 1 (Nat.pair (Nat.pair 0 (encodeInt numerator)) (encodeNat denominator)):=by
    unfold rationalTupleOutput taggedTupleOutput code
    rw [show (2 : ℕ)=[encodeInt numerator,encodeNat denominator].length by rfl]
    rw [decodeTaggedTuple_encode]
    rfl
  by_cases hn:numerator<0
  · have hm:numerator.natAbs≠0:=Int.natAbs_ne_zero.mpr (by omega)
    simp [rationalValidationAccepts,rationalTupleFlag,htuple,rationalTupleFields,
      rationalNumeratorFrame,rationalNumeratorCode,rationalDenominatorCode,rationalSign,
      rationalMagnitudeCode,rationalMagnitudeFlag,rationalMagnitudeValidation,rationalMagnitudeValue,
      rationalDenominatorFlag,rationalDenominatorValidation,rationalDenominatorValue,rationalGcdValue,
      encodeInt,hn,hm]
  · simp [rationalValidationAccepts,rationalTupleFlag,htuple,rationalTupleFields,
      rationalNumeratorFrame,rationalNumeratorCode,rationalDenominatorCode,rationalSign,
      rationalMagnitudeCode,rationalMagnitudeFlag,rationalMagnitudeValidation,rationalMagnitudeValue,
      rationalDenominatorFlag,rationalDenominatorValidation,rationalDenominatorValue,rationalGcdValue,
      encodeInt,hn]

theorem decode_code_iff (numerator : ℤ) (denominator : ℕ) :
    (∃ coefficient,decodeCanonicalRational (code numerator denominator)=some coefficient) ↔
      denominator≠0 ∧ numerator.natAbs.gcd denominator=1:=
  (rationalValidationAccepts_iff_decodeCanonicalRational _).symm.trans (code_accepts numerator denominator)

theorem accepted_fields (numerator : ℤ) (denominator : ℕ) (coefficient : ℚ)
    (hd : decodeCanonicalRational (code numerator denominator)=some coefficient) :
    coefficient.num=numerator ∧ coefficient.den=denominator:=by
  have h:=congrArg decodeTaggedList (encodeCanonicalRational_of_decode hd)
  simp only [encodeCanonicalRational,code,decodeTaggedList_encode] at h
  have hp:=List.cons.inj (Option.some.inj h)
  have hn:=congrArg decodeInt hp.1
  have hd:=congrArg decodeNat (List.cons.inj hp.2).1
  exact ⟨by simpa only [decodeInt_encode,Option.some.injEq] using hn,
    by simpa only [decodeNat_encode,Option.some.injEq] using hd⟩

theorem all_raw_iff (raw : ℕ) :
    (∃ coefficient,decodeCanonicalRational raw=some coefficient) ↔
      ∃ numerator denominator,raw=code numerator denominator ∧
        denominator≠0 ∧ numerator.natAbs.gcd denominator=1:=by
  constructor
  · rintro ⟨coefficient,hc⟩
    exact ⟨coefficient.num,coefficient.den,(encodeCanonicalRational_of_decode hc).symm,
      coefficient.den_nz,coefficient.reduced.gcd_eq_one⟩
  · rintro ⟨numerator,denominator,rfl,hd,hgcd⟩
    exact (decode_code_iff numerator denominator).mpr ⟨hd,hgcd⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.RationalFields
