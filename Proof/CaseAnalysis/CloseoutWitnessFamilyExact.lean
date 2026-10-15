import Proof.CaseAnalysis.WitnessSumAccepted
import Proof.CaseAnalysis.WitnessFamilySeal

/-! The physical exact-V family test is equivalent to the original
canonical typed family decoder, in the same ordered proof-variable list. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyExact
open CanonicalWitnessCodec CanonicalBinary RadixSemantics
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
theorem decoded_list (words : List (List Bool)) (arity : List Bool)
    (ha:value arity=limits.expectedArity) (hb:1 ≤ limits.coefficientBitCap)
    (h:FamilyLoop.passed C limits.termCap limits.coefficientMassCap words arity circuitPass=true) :
    ∃ ss : List (CheckedLegalCircuitSum Circuit wires description limits),
      words.map value=ss.map (·.code codec) := by
  induction words with
  | nil=>exact ⟨[],rfl⟩
  | cons bits words ih=>
    have both:=Bool.and_eq_true_iff.mp h
    obtain ⟨checked,hdecode⟩:=SumExact.decoded codec wires description limits C hC circuitPass hcircuit
      bits arity ha hb both.1
    obtain ⟨ss,hcodes⟩:=ih both.2
    refine ⟨checked::ss,?_⟩
    simp only [List.map_cons,CheckedLegalCircuitSum.code_of_decode hdecode,hcodes]

include hC hcircuit in
theorem passed_iff_decoded (V : ℕ) (bits arity : List Bool)
    (ha:value arity=limits.expectedArity) (hb:1 ≤ limits.coefficientBitCap) :
    FamilyRun.passed V C limits.termCap limits.coefficientMassCap bits arity circuitPass=true ↔
      ∃ family,SumFamily.decode codec wires description limits V (value bits)=some family := by
  constructor
  · intro h
    have both:=Bool.and_eq_true_iff.mp h
    obtain ⟨ss,hcodes⟩:=decoded_list codec wires description limits C hC circuitPass hcircuit
      (FamilyFields.words bits) arity ha hb both.2
    obtain ⟨family,hdecode,_⟩:=FamilySeal.checked_family codec wires description limits V bits ss both.1
      ((Reencode.fields_values bits).symm.trans hcodes)
    exact ⟨family,hdecode⟩
  · rintro ⟨family,hdecode⟩
    have code:=SumFamily.code_of_decode codec hdecode
    have codes : encodeBalancedList (family.sums.map (fun checked=>checked.code codec))=value bits := code
    have count:FamilyCount.accepted bits V=true:=(FamilyCount.decision_exact bits V).mpr
      ⟨family.sums.map (fun checked=>checked.code codec),codes,by rw [List.length_map,family.length_eq]⟩
    have words:(FamilyFields.words bits).map value=family.sums.map (·.code codec):=
      (Reencode.fields_values bits).trans (by rw [←code];exact PCPPNativeCanonicalTree.tree_atoms _)
    apply Bool.and_eq_true_iff.mpr
    refine ⟨count,?_⟩
    change (FamilyFields.words bits).all (fun field=>SumRound.passed C limits.termCap
      limits.coefficientMassCap field arity circuitPass)=true
    rw [List.all_eq_true]
    intro field hf
    have member:value field∈family.sums.map (·.code codec):=
      words ▸ List.mem_map.mpr ⟨field,hf,rfl⟩
    obtain ⟨checked,_hc,hcode⟩:=List.mem_map.mp member
    apply (SumExact.passed_iff_decoded codec wires description limits C hC circuitPass hcircuit field arity ha hb).mpr
    refine ⟨checked,?_⟩
    rw [←hcode]
    exact decodeLegalCircuitSum_encode codec wires description limits checked

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyExact
