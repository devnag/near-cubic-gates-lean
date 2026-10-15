import Proof.CaseAnalysis.WitnessSumSeal
import Proof.CaseAnalysis.WitnessFamilyMode

/-! The executed term choices and mass fold yield the original typed sum,
including its canonical code. No semantic range test is imposed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumExact
open CanonicalWitnessCodec CanonicalBinary RadixSemantics CompetitorSumFold CompetitorSumWidth
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable {Circuit : SupplierPipeline.CircuitFamily}
variable (codec : CanonicalCircuitCodec Circuit) (wires description : {n : ℕ}→Circuit n→ℕ)
variable (limits : LegalSumLimits) (C : ℕ) (hC:limits.coefficientBitCap=natBitLength C)
variable (circuitPass : List Bool→Bool)
variable (hcircuit:∀ bits,circuitPass bits=true ↔ ∃ c,
  codec.decode limits.expectedArity (value (TermCoefficient.circuitCode bits))=some c ∧
    wires c ≤ limits.wireCap ∧ description c ≤ limits.descriptionCap)

include hC hcircuit in
theorem term (bits : List Bool) (h:TermRoundAll.accepted C bits (circuitPass bits)=true) :
    ∃ t : LegalCircuitTerm Circuit limits.expectedArity,
      t.code codec=value bits ∧ TermChoice.rational (natBitLength C) bits=t.coefficient ∧
      natBitLength t.coefficient.num.natAbs ≤ limits.coefficientBitCap ∧
      natBitLength t.coefficient.den ≤ limits.coefficientBitCap ∧
      wires t.circuit ≤ limits.wireCap ∧ description t.circuit ≤ limits.descriptionCap := by
  classical
  have both:=Bool.and_eq_true_iff.mp h
  obtain ⟨header,q,hq,hn,hd⟩:=(TermChoice.coefficient_isSome _ _).mp both.1
  obtain ⟨c,hc,hw,hl⟩:=(hcircuit bits).mp both.2
  have shape: value bits=encodeTaggedList
      [value (TermCoefficient.coefficientCode bits),value (TermCoefficient.circuitCode bits)]:=
    (PairHeader.valid_iff bits).mp header
  rw [←encodeCanonicalRational_of_decode hq,←codec.encode_decode hc] at shape
  refine ⟨⟨q,c⟩,shape.symm,?_,by simpa only [hC] using hn,by simpa only [hC] using hd,hw,hl⟩
  exact TermChoice.rational_eq _ _ q ((TermChoice.coefficient_some _ _ _).mpr ⟨header,hq,hn,hd⟩)

include hC hcircuit in
theorem terms (words : List (List Bool)) (h:TermLoop.passed C words circuitPass=true) :
    ∃ ts : List (LegalCircuitTerm Circuit limits.expectedArity),
      words.map value=ts.map (·.code codec) ∧
      words.map (TermChoice.rational (natBitLength C))=ts.map (·.coefficient) ∧
      ∀ t∈ts,natBitLength t.coefficient.num.natAbs ≤ limits.coefficientBitCap ∧
        natBitLength t.coefficient.den ≤ limits.coefficientBitCap ∧
        wires t.circuit ≤ limits.wireCap ∧ description t.circuit ≤ limits.descriptionCap := by
  induction words with
  | nil=>exact ⟨[],rfl,rfl,by simp⟩
  | cons bits words ih=>
    have both:TermRoundAll.accepted C bits (circuitPass bits)=true ∧ TermLoop.passed C words circuitPass=true:=
      Bool.and_eq_true_iff.mp h
    obtain ⟨t,ht,hq,hb,hd,hw,hl⟩:=term codec wires description limits C hC circuitPass hcircuit bits both.1
    obtain ⟨ts,hcodes,hcoeffs,hvalid⟩:=ih both.2
    refine ⟨t::ts,?_,?_,?_⟩
    · simp only [List.map_cons,ht,hcodes]
    · simp only [List.map_cons,hq,hcoeffs]
    · intro v hv
      rcases List.mem_cons.mp hv with rfl|hv
      · exact ⟨hb,hd,hw,hl⟩
      · exact hvalid v hv

theorem mass_records (words : List (List Bool))
    (ts : List (LegalCircuitTerm Circuit limits.expectedArity))
    (hcoeffs:words.map (TermChoice.rational (natBitLength C))=ts.map (·.coefficient)) :
    TermLoop.mass C words words.length=folded zero (Mass.records (ts.map (·.coefficient))) := by
  unfold TermLoop.mass
  rw [List.take_length]
  change folded zero (words.map (Mass.magnitude ∘ TermChoice.rational (natBitLength C)))=_
  rw [←List.map_map,hcoeffs]
  rfl

include hC hcircuit in
theorem decoded (bits arity : List Bool) (ha:value arity=limits.expectedArity)
    (hb:1 ≤ limits.coefficientBitCap)
    (h:SumRound.passed C limits.termCap limits.coefficientMassCap bits arity circuitPass=true) :
    ∃ checked,decodeLegalCircuitSum codec wires description limits (value bits)=some checked := by
  classical
  have both:=Bool.and_eq_true_iff.mp h
  have header:SumGuard.Passes bits arity limits.termCap:=of_decide_eq_true both.1
  have body:=Bool.and_eq_true_iff.mp both.2
  obtain ⟨ts,hcodes,hcoeffs,hvalid⟩:=terms codec wires description limits C hC circuitPass hcircuit _ body.1
  have atoms:SumFields.atoms bits=ts.map (·.code codec):=
    (Reencode.fields_values (SumFields.listCode bits)).symm.trans hcodes
  have hmass:(folded zero (Mass.records (ts.map (·.coefficient)))).value ≤ limits.coefficientMassCap:=by
    rw [←mass_records limits C _ ts hcoeffs]
    exact of_decide_eq_true body.2
  obtain ⟨checked,hchecked,_⟩:=SumSeal.checked_sum codec wires description limits bits arity ts header ha atoms hb
    (fun t ht=>⟨(hvalid t ht).1,(hvalid t ht).2.1⟩) hmass
    (fun t ht=>(hvalid t ht).2.2.1) (fun t ht=>(hvalid t ht).2.2.2)
  exact ⟨checked,hchecked⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SumExact
