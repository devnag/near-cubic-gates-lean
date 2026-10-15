import Proof.CaseAnalysis.WitnessSumDecoded

/-! A canonical typed legal sum passes the same executed guards and
mass comparison. Together with decoded this gives both directions. -/
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
theorem term_of_code (bits : List Bool) (t : LegalCircuitTerm Circuit limits.expectedArity)
    (hcode:t.code codec=value bits)
    (hn:natBitLength t.coefficient.num.natAbs ≤ limits.coefficientBitCap)
    (hd:natBitLength t.coefficient.den ≤ limits.coefficientBitCap)
    (hw:wires t.circuit ≤ limits.wireCap) (hl:description t.circuit ≤ limits.descriptionCap) :
    TermRoundAll.accepted C bits (circuitPass bits)=true ∧
      TermChoice.rational (natBitLength C) bits=t.coefficient := by
  obtain ⟨header,qcode,ccode⟩:=PairHeader.extracted_values bits
    (encodeCanonicalRational t.coefficient) (codec.encode t.circuit) hcode.symm
  change value (TermCoefficient.coefficientCode bits)=_ at qcode
  change value (TermCoefficient.circuitCode bits)=_ at ccode
  have qdecode:decodeCanonicalRational (value (TermCoefficient.coefficientCode bits))=some t.coefficient:=by
    rw [qcode];exact decodeCanonicalRational_encode _
  have coeff:TermChoice.coefficient (natBitLength C) bits=some t.coefficient:=
    (TermChoice.coefficient_some _ _ _).mpr ⟨header,qdecode,hC ▸ hn,hC ▸ hd⟩
  have circuit:circuitPass bits=true:=(hcircuit bits).mpr
    ⟨t.circuit,by rw [ccode];exact codec.decode_encode _,hw,hl⟩
  refine ⟨?_,TermChoice.rational_eq _ _ _ coeff⟩
  simp only [TermRoundAll.accepted,coeff,Option.isSome_some,circuit,Bool.and_self]

include hC hcircuit in
theorem words_of_codes (words : List (List Bool))
    (ts : List (LegalCircuitTerm Circuit limits.expectedArity))
    (hcodes:words.map value=ts.map (·.code codec))
    (hvalid:∀ t∈ts,natBitLength t.coefficient.num.natAbs ≤ limits.coefficientBitCap ∧
      natBitLength t.coefficient.den ≤ limits.coefficientBitCap ∧
      wires t.circuit ≤ limits.wireCap ∧ description t.circuit ≤ limits.descriptionCap) :
    TermLoop.passed C words circuitPass=true ∧
      words.map (TermChoice.rational (natBitLength C))=ts.map (·.coefficient) := by
  induction words generalizing ts with
  | nil=>
    cases ts
    · exact ⟨rfl,rfl⟩
    · cases hcodes
  | cons bits words ih=>
    cases ts with
    | nil=>simp only [List.map_nil,List.map_cons,List.cons_ne_nil] at hcodes
    | cons t ts=>
      have codes:=List.cons.inj hcodes
      have valid:=hvalid t (by simp)
      obtain ⟨yes,rational⟩:=term_of_code codec wires description limits C hC circuitPass hcircuit bits t
        codes.1.symm valid.1 valid.2.1 valid.2.2.1 valid.2.2.2
      obtain ⟨tail,coeffs⟩:=ih ts codes.2 (fun t ht=>hvalid t (List.mem_cons_of_mem _ ht))
      refine ⟨?_,?_⟩
      · change (TermRoundAll.accepted C bits (circuitPass bits) && TermLoop.passed C words circuitPass)=true
        rw [yes,tail]
        rfl
      · simp only [List.map_cons,rational,coeffs]

include hC hcircuit in
theorem passed_of_code (bits arity : List Bool) (ha:value arity=limits.expectedArity)
    (hb:1 ≤ limits.coefficientBitCap) (ts : List (LegalCircuitTerm Circuit limits.expectedArity))
    (hcode:value bits=encodeTaggedList [encodeNat limits.expectedArity,encodeBalancedList (ts.map (·.code codec))])
    (hlen:ts.length ≤ limits.termCap)
    (hbits:∀ t∈ts,natBitLength t.coefficient.num.natAbs ≤ limits.coefficientBitCap ∧
      natBitLength t.coefficient.den ≤ limits.coefficientBitCap)
    (hmass:(LegalCircuitSumDescription.mk limits.expectedArity ts).coefficientMass ≤ limits.coefficientMassCap)
    (hwires:∀ t∈ts,wires t.circuit ≤ limits.wireCap)
    (hdescription:∀ t∈ts,description t.circuit ≤ limits.descriptionCap) :
    SumRound.passed C limits.termCap limits.coefficientMassCap bits arity circuitPass=true := by
  classical
  have header:SumGuard.Passes bits arity limits.termCap:=(SumGuard.passes_code _ _ _).mpr
    ⟨ts.map (·.code codec),by rw [ha];exact hcode,by simpa only [List.length_map] using hlen⟩
  obtain ⟨_,_,listCode⟩:=PairHeader.extracted_values bits _ _ hcode
  change value (SumFields.listCode bits)=encodeBalancedList (ts.map (·.code codec)) at listCode
  have words:(SumHeader.words bits).map value=ts.map (·.code codec):=
    (Reencode.fields_values (SumFields.listCode bits)).trans (by rw [listCode,PCPPNativeCanonicalTree.tree_atoms])
  obtain ⟨yes,coeffs⟩:=words_of_codes codec wires description limits C hC circuitPass hcircuit _ ts words
    (fun t ht=>⟨(hbits t ht).1,(hbits t ht).2,hwires t ht,hdescription t ht⟩)
  obtain ⟨trace,values⟩:=Mass.rational_trace limits.termCap limits.coefficientBitCap
    (ts.map (·.coefficient)) hb (by simpa only [List.length_map] using hlen) (by
      intro q hq;obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hq;exact hbits t ht)
  have total:=folded_value (width limits.termCap limits.coefficientBitCap) zero
    (Mass.records (ts.map (·.coefficient))) trace
  have zeroValue:zero.value=0:=by simp [zero,CompetitorValidity.Estimate.value]
  rw [zeroValue,zero_add,values] at total
  have bound:(TermLoop.mass C (SumHeader.words bits) (SumHeader.words bits).length).value ≤ limits.coefficientMassCap:=by
    rw [mass_records limits C _ ts coeffs,total]
    change ts.foldl (fun sum t=>sum+|t.coefficient|) 0 ≤ _ at hmass
    simpa only [Average.mass_fold,Average.mass,List.map_map,Function.comp_def] using hmass
  simp only [SumRound.passed,SumHeader.flag,header,decide_true,Bool.true_and,
    SumBody.passed,yes,decide_eq_true_eq]
  exact bound

include hC hcircuit in
theorem passed_iff_decoded (bits arity : List Bool) (ha:value arity=limits.expectedArity)
    (hb:1 ≤ limits.coefficientBitCap) :
    SumRound.passed C limits.termCap limits.coefficientMassCap bits arity circuitPass=true ↔
      ∃ checked,decodeLegalCircuitSum codec wires description limits (value bits)=some checked := by
  constructor
  · exact decoded codec wires description limits C hC circuitPass hcircuit bits arity ha hb
  · rintro ⟨checked,hdecode⟩
    have code:=CheckedLegalCircuitSum.code_of_decode hdecode
    rcases checked with ⟨⟨core,ts⟩,hcore,hlen,hbits,hmass,hw,hl⟩
    dsimp only at hcore
    subst core
    exact passed_of_code codec wires description limits C hC circuitPass hcircuit bits arity ha hb ts
      code.symm hlen hbits hmass hw hl

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SumExact
