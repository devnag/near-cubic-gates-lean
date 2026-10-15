import Proof.CaseAnalysis.WitnessMassActual
import Proof.CaseAnalysis.WitnessSumMeaning
import Proof.CaseAnalysis.WitnessAverage

/-! The executed sum header, ordered term identities and exact mass
accumulator discharge the original public checked-sum decoder directly. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumSeal
open CanonicalWitnessCodec CanonicalBinary RadixSemantics
open CompetitorSumFold CompetitorSumWidth
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem checked_sum {Circuit : CircuitFamily} (codec : CanonicalCircuitCodec Circuit)
    (wires description : {n : ℕ}→Circuit n→ℕ) (limits : LegalSumLimits)
    (bits arityBits : List Bool) (ts : List (LegalCircuitTerm Circuit limits.expectedArity))
    (hheader : SumGuard.Passes bits arityBits limits.termCap)
    (harity : value arityBits=limits.expectedArity)
    (hcodes : SumFields.atoms bits=ts.map (·.code codec))
    (hb : 1≤limits.coefficientBitCap)
    (hbits : ∀ t∈ts,natBitLength t.coefficient.num.natAbs≤limits.coefficientBitCap ∧
      natBitLength t.coefficient.den≤limits.coefficientBitCap)
    (hmass : (folded zero (Mass.records (ts.map (·.coefficient)))).value≤limits.coefficientMassCap)
    (hwires : ∀ t∈ts,wires t.circuit≤limits.wireCap)
    (hdescription : ∀ t∈ts,description t.circuit≤limits.descriptionCap) :
    ∃ checked : CheckedLegalCircuitSum Circuit wires description limits,
      decodeLegalCircuitSum codec wires description limits (value bits)=some checked ∧
      checked.value=⟨limits.expectedArity,ts⟩:=by
  obtain ⟨hshape,hcount⟩:=SumGuard.accepted_atoms bits arityBits limits.termCap hheader
  rw [hcodes,List.length_map] at hcount
  have hcoeffs:∀ q∈ts.map (·.coefficient),
      natBitLength q.num.natAbs≤limits.coefficientBitCap ∧ natBitLength q.den≤limits.coefficientBitCap:=by
    intro q hq
    obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hq
    exact hbits t ht
  obtain ⟨htrace,hvalue⟩:=Mass.rational_trace limits.termCap limits.coefficientBitCap
    (ts.map (·.coefficient)) hb (by simpa only [List.length_map] using hcount) hcoeffs
  have hv:=folded_value (width limits.termCap limits.coefficientBitCap) zero
    (Mass.records (ts.map (·.coefficient))) htrace
  have hz:zero.value=0:=by simp [zero,CompetitorValidity.Estimate.value]
  rw [hz,zero_add,hvalue] at hv
  have hm:(LegalCircuitSumDescription.mk limits.expectedArity ts).coefficientMass≤limits.coefficientMassCap:=by
    change ts.foldl (fun total t=>total+|t.coefficient|) 0≤_
    rw [Average.mass_fold]
    have he:Average.mass ts=((ts.map (·.coefficient)).map (fun q=>|q|)).sum:=by
      simp only [Average.mass,List.map_map,Function.comp_def]
    rw [he,←hv]
    exact hmass
  let checked : CheckedLegalCircuitSum Circuit wires description limits:=
    { value:=⟨limits.expectedArity,ts⟩
      arity_eq:=rfl
      terms_le:=hcount
      coefficient_bits_le:=hbits
      mass_le:=hm
      wires_le:=hwires
      description_le:=hdescription }
  have hcode:checked.code codec=value bits:=by
    change encodeTaggedList [encodeNat limits.expectedArity,encodeBalancedList (ts.map (·.code codec))]=_
    rw [harity,hcodes] at hshape
    exact hshape.symm
  refine ⟨checked,?_,rfl⟩
  rw [←hcode]
  exact decodeLegalCircuitSum_encode codec wires description limits checked

end NearCubicWires.RepairOrdinary.CloseoutWitness.SumSeal
