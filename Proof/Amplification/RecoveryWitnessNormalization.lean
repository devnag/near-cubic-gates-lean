import Proof.Foundations.RecoveryPipeline
import Proof.Amplification.RecoveryWitnessPolicy

/-!
# Canonical normalization of XOR-authorized recovery sums

The XOR theorem speaks about semantic rational sums over the two physical
wire families, while the fixed weak machine decodes normalized canonical
syntax.  This module is the sole bridge between those representations.  Every
finite cap is derived from the XOR witness and the source wire bound; callers
provide no alternate encoding, normalization, or resource envelope.
-/

namespace NearCubicWires.RecoveryWitnessNormalization

open NearCubicWires
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.CircuitRestriction
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

/-- Exact term envelope authorized by the imported XOR theorem. -/
noncomputable def xorAuthorizedTermCap
    (witness : XorAmplificationWitness) (delta : ℝ)
    (copies arity : ℕ) : ℕ :=
  ⌈witness.termCoefficient delta * arity /
    xorEpsilon delta copies ^ 2⌉₊

/-- Exact rational encoding envelope authorized by the XOR theorem. -/
def xorAuthorizedCoefficientBitCap
    (witness : XorAmplificationWitness) (delta : ℝ)
    (arity : ℕ) : ℕ :=
  xorCoefficientBitBound witness.coefficientBitCoefficient
    witness.coefficientBitDegree delta arity

/-- Exact real coefficient-mass envelope in the XOR premise. -/
noncomputable def xorAuthorizedCoefficientMass
    (witness : XorAmplificationWitness) (delta : ℝ)
    (copies : ℕ) : ℝ :=
  witness.massCoefficient delta / xorEpsilon delta copies

/-- The finite decoder uses the least natural, represented canonically as a
rational, that dominates the source theorem's real mass envelope. -/
noncomputable def xorAuthorizedRationalMassCap
    (witness : XorAmplificationWitness) (delta : ℝ)
    (copies : ℕ) : ℚ :=
  (⌈xorAuthorizedCoefficientMass witness delta copies⌉₊ : ℚ)

/-- Frozen decoder limits for the normalized `SYM ∘ THR` branch. -/
noncomputable def symmetricXorLegalSumLimits
    (witness : XorAmplificationWitness) (delta : ℝ)
    (copies arity wireCap : ℕ) : LegalSumLimits where
  expectedArity := arity
  termCap := xorAuthorizedTermCap witness delta copies arity
  coefficientBitCap := xorAuthorizedCoefficientBitCap witness delta arity
  coefficientMassCap :=
    xorAuthorizedRationalMassCap witness delta copies
  wireCap := wireCap
  descriptionCap := symmetricDescriptionCap arity wireCap

/-- Frozen decoder limits for the support-compressed, normalized
`THR ∘ THR` branch. -/
noncomputable def thresholdXorLegalSumLimits
    (witness : XorAmplificationWitness) (delta : ℝ)
    (copies arity wireCap : ℕ) : LegalSumLimits where
  expectedArity := arity
  termCap := xorAuthorizedTermCap witness delta copies arity
  coefficientBitCap := xorAuthorizedCoefficientBitCap witness delta arity
  coefficientMassCap :=
    xorAuthorizedRationalMassCap witness delta copies
  wireCap := wireCap
  descriptionCap := thresholdDescriptionCap arity wireCap

/-- The complete frozen witness policy keeps the outer oracle arity distinct
from the arity of every atom in the decoded rational sum. -/
noncomputable def xorRecoveryWitnessLimits
    (witness : XorAmplificationWitness) (delta : ℝ) (copies : ℕ)
    (oracleArity oracleSizeCap sumArity
      symmetricWireCap thresholdWireCap : ℕ) :
    RecoveryWitnessLimits where
  oracleArity := oracleArity
  oracleSizeCap := oracleSizeCap
  sumArity := sumArity
  symmetric :=
    symmetricXorLegalSumLimits witness delta copies
      sumArity symmetricWireCap
  threshold :=
    thresholdXorLegalSumLimits witness delta copies
      sumArity thresholdWireCap
  symmetricArity := rfl
  thresholdArity := rfl

private theorem rationalCoefficientMass_cast
    {Function : Type} (terms : List (ℚ × Function)) :
    ((terms.foldl (fun total term => total + |term.1|) 0 : ℚ) : ℝ) =
      terms.foldl
        (fun total term => total + |(term.1 : ℝ)|) 0 := by
  have general :
      ∀ (terms : List (ℚ × Function)) (initial : ℚ),
        ((terms.foldl
            (fun total term => total + |term.1|) initial : ℚ) : ℝ) =
          terms.foldl
            (fun total term => total + |(term.1 : ℝ)|) (initial : ℝ) := by
    intro remaining
    induction remaining with
    | nil =>
        intro initial
        rfl
    | cons term remaining inductionHypothesis =>
        intro initial
        simp only [List.foldl_cons]
        rw [inductionHypothesis]
        norm_cast
  simpa using general terms 0

private theorem rationalCoefficientMass_le_ceil
    {family : SizedFunctionFamily} {arity wireCap : ℕ}
    (sum : UnitIntervalCircuitSum family arity wireCap)
    (mass : ℝ) (hmass : sum.coefficientMass ≤ mass) :
    sum.terms.foldl (fun total term => total + |term.1|) 0 ≤
      (⌈mass⌉₊ : ℚ) := by
  have hceil : mass ≤ (⌈mass⌉₊ : ℝ) := Nat.le_ceil mass
  have hreal :
      ((sum.terms.foldl
          (fun total term => total + |term.1|) 0 : ℚ) : ℝ) ≤
        (((⌈mass⌉₊ : ℕ) : ℚ) : ℝ) := by
    rw [rationalCoefficientMass_cast]
    exact hmass.trans hceil
  exact_mod_cast hreal

private theorem existsNormalizedSymmetricAtom
    (normalization : ThresholdNormalizationContract)
    {arity wireCap : ℕ} {function : BoolFunction arity}
    (legal : symmetricWireFamily arity function wireCap) :
    ∃ circuit : NormalizedSymmetricThresholdCircuit arity,
      circuit.eval = function ∧
        circuit.wireCount ≤ wireCap ∧
        circuit.descriptionBits ≤
          symmetricDescriptionCap arity wireCap := by
  rcases legal with ⟨source, hwires, heval⟩
  rcases normalizeSymmetricCircuit normalization source with
    ⟨target, htargetEval, htargetWires, hparameters⟩
  refine ⟨target, ?_, htargetWires.le.trans hwires, ?_⟩
  · funext input
    rw [htargetEval input, heval]
  · exact normalizedSymmetric_descriptionBits_le target
      (htargetWires.le.trans hwires) hparameters

private theorem existsNormalizedThresholdAtom
    (normalization : ThresholdNormalizationContract)
    {arity wireCap : ℕ} {function : BoolFunction arity}
    (legal : thresholdWireFamily arity function wireCap) :
    ∃ circuit : NormalizedThresholdThresholdCircuit arity,
      circuit.eval = function ∧
        circuit.wireCount ≤ wireCap ∧
        circuit.descriptionBits ≤
          thresholdDescriptionCap arity wireCap := by
  rcases legal with ⟨source, hwires, heval⟩
  rcases existsCompressedNormalizedThresholdCircuit normalization source with
    ⟨target, htargetEval, htargetWires, hbottomCount,
      hbottom, htop⟩
  refine ⟨target, ?_, htargetWires.le.trans hwires, ?_⟩
  · funext input
    rw [htargetEval input, heval]
  · exact normalizedThreshold_descriptionBits_le target
      (hbottomCount.trans hwires) hbottom htop

/-- Normalize every occurrence of an XOR-authorized `SYM ∘ THR` sum into the
canonical decoder type.  Coefficient order is unchanged, and the resulting
rational combination agrees pointwise with the semantic source sum. -/
theorem symmetricCheckedLegalCircuitSum_of_contracts
    (normalization : ThresholdNormalizationContract)
    (witness : XorAmplificationWitness) (delta : ℝ)
    (copies : ℕ) {arity wireCap : ℕ}
    (sum : UnitIntervalCircuitSum symmetricWireFamily arity wireCap)
    (hterms :
      sum.terms.length ≤
        xorAuthorizedTermCap witness delta copies arity)
    (hbits :
      sum.coefficientsWithinBitBound
        (xorAuthorizedCoefficientBitCap witness delta arity))
    (hmass :
      sum.coefficientMass ≤
        xorAuthorizedCoefficientMass witness delta copies) :
    ∃ checked : CheckedLegalCircuitSum
        NormalizedSymmetricThresholdCircuit
        NormalizedSymmetricThresholdCircuit.wireCount
        NormalizedSymmetricThresholdCircuit.descriptionBits
        (symmetricXorLegalSumLimits witness delta copies arity wireCap),
      checked.value.terms.map (·.coefficient) =
          sum.terms.map (·.1) ∧
        ∀ input,
          checked.value.terms.foldl
              (fun total term =>
                total + (term.coefficient : ℝ) *
                  bitAsReal (term.circuit.eval input)) 0 =
            sum.value
              (cast (congrArg BitInput checked.arity_eq) input) := by
  classical
  have normalized :
      ∀ term : {term // term ∈ sum.terms},
        ∃ circuit : NormalizedSymmetricThresholdCircuit arity,
          circuit.eval = term.val.2 ∧
            circuit.wireCount ≤ wireCap ∧
            circuit.descriptionBits ≤
              symmetricDescriptionCap arity wireCap := by
    intro term
    exact existsNormalizedSymmetricAtom normalization
      (sum.legal term.val term.property)
  let circuitFor :
      {term // term ∈ sum.terms} →
        NormalizedSymmetricThresholdCircuit arity :=
    fun term => Classical.choose (normalized term)
  have circuitFor_spec (term : {term // term ∈ sum.terms}) :
      (circuitFor term).eval = term.val.2 ∧
        (circuitFor term).wireCount ≤ wireCap ∧
        (circuitFor term).descriptionBits ≤
          symmetricDescriptionCap arity wireCap :=
    Classical.choose_spec (normalized term)
  let canonicalTerms :
      List (LegalCircuitTerm NormalizedSymmetricThresholdCircuit arity) :=
    sum.terms.attach.map fun term =>
      { coefficient := term.val.1
        circuit := circuitFor term }
  let description :
      LegalCircuitSumDescription NormalizedSymmetricThresholdCircuit :=
    { q := arity
      terms := canonicalTerms }
  have hcanonicalTermsLength :
      canonicalTerms.length = sum.terms.length := by
    simp [canonicalTerms]
  have hcanonicalMass :
      description.coefficientMass =
        sum.terms.foldl (fun total term => total + |term.1|) 0 := by
    simp only [description, LegalCircuitSumDescription.coefficientMass,
      canonicalTerms, List.foldl_map]
    simpa only [List.foldl_map] using
      congrArg
        (fun masses : List ℚ => masses.foldl (· + ·) 0)
        (List.attach_map_val
          (l := sum.terms)
          (f := fun term : ℚ × BoolFunction arity => |term.1|))
  have hcanonicalCoefficients :
      canonicalTerms.map (·.coefficient) =
        sum.terms.map (·.1) := by
    simp only [canonicalTerms, List.map_map]
    exact
      List.attach_map_val
        (l := sum.terms)
        (f := fun term : ℚ × BoolFunction arity => term.1)
  let checked : CheckedLegalCircuitSum
      NormalizedSymmetricThresholdCircuit
      NormalizedSymmetricThresholdCircuit.wireCount
      NormalizedSymmetricThresholdCircuit.descriptionBits
      (symmetricXorLegalSumLimits witness delta copies arity wireCap) :=
    { value := description
      arity_eq := rfl
      terms_le := by
        rw [hcanonicalTermsLength]
        exact hterms
      coefficient_bits_le := by
        intro term hterm
        rcases List.mem_map.mp hterm with
          ⟨sourceTerm, _, rfl⟩
        exact hbits sourceTerm.val sourceTerm.property
      mass_le := by
        rw [hcanonicalMass]
        exact rationalCoefficientMass_le_ceil sum
          (xorAuthorizedCoefficientMass witness delta copies) hmass
      wires_le := by
        intro term hterm
        rcases List.mem_map.mp hterm with
          ⟨sourceTerm, _, rfl⟩
        exact (circuitFor_spec sourceTerm).2.1
      description_le := by
        intro term hterm
        rcases List.mem_map.mp hterm with
          ⟨sourceTerm, _, rfl⟩
        exact (circuitFor_spec sourceTerm).2.2 }
  refine ⟨checked, ?_, ?_⟩
  · simpa only [checked, description] using hcanonicalCoefficients
  · intro input
    change BitInput arity at input
    have foldCorrespondence :
        ∀ (terms : List {term // term ∈ sum.terms}) (initial : ℝ),
          (terms.map fun term =>
              ({ coefficient := term.val.1
                 circuit := circuitFor term } :
                LegalCircuitTerm
                  NormalizedSymmetricThresholdCircuit arity)).foldl
                (fun total term =>
                  total + (term.coefficient : ℝ) *
                    bitAsReal (term.circuit.eval input)) initial =
            terms.foldl
              (fun total term =>
                total + (term.val.1 : ℝ) *
                  bitAsReal (term.val.2 input)) initial := by
      intro terms
      induction terms with
      | nil =>
          intro initial
          rfl
      | cons term terms inductionHypothesis =>
          intro initial
          simp only [List.map_cons, List.foldl_cons]
          rw [congrFun (circuitFor_spec term).1 input]
          exact inductionHypothesis _
    change
      canonicalTerms.foldl
          (fun total term =>
            total + (term.coefficient : ℝ) *
              bitAsReal (term.circuit.eval input)) 0 =
        sum.value input
    rw [foldCorrespondence sum.terms.attach 0]
    unfold UnitIntervalCircuitSum.value
    simpa only [List.foldl_map] using
      congrArg
        (fun contributions : List ℝ =>
          contributions.foldl (· + ·) 0)
        (List.attach_map_val
          (l := sum.terms)
          (f := fun term : ℚ × BoolFunction arity =>
            (term.1 : ℝ) * bitAsReal (term.2 input)))

/-- Normalize every occurrence of an XOR-authorized `THR ∘ THR` sum after
compressing unused top support.  The checked syntax preserves coefficient
order and the complete pointwise rational combination. -/
theorem thresholdCheckedLegalCircuitSum_of_contracts
    (normalization : ThresholdNormalizationContract)
    (witness : XorAmplificationWitness) (delta : ℝ)
    (copies : ℕ) {arity wireCap : ℕ}
    (sum : UnitIntervalCircuitSum thresholdWireFamily arity wireCap)
    (hterms :
      sum.terms.length ≤
        xorAuthorizedTermCap witness delta copies arity)
    (hbits :
      sum.coefficientsWithinBitBound
        (xorAuthorizedCoefficientBitCap witness delta arity))
    (hmass :
      sum.coefficientMass ≤
        xorAuthorizedCoefficientMass witness delta copies) :
    ∃ checked : CheckedLegalCircuitSum
        NormalizedThresholdThresholdCircuit
        NormalizedThresholdThresholdCircuit.wireCount
        NormalizedThresholdThresholdCircuit.descriptionBits
        (thresholdXorLegalSumLimits witness delta copies arity wireCap),
      checked.value.terms.map (·.coefficient) =
          sum.terms.map (·.1) ∧
        ∀ input,
          checked.value.terms.foldl
              (fun total term =>
                total + (term.coefficient : ℝ) *
                  bitAsReal (term.circuit.eval input)) 0 =
            sum.value
              (cast (congrArg BitInput checked.arity_eq) input) := by
  classical
  have normalized :
      ∀ term : {term // term ∈ sum.terms},
        ∃ circuit : NormalizedThresholdThresholdCircuit arity,
          circuit.eval = term.val.2 ∧
            circuit.wireCount ≤ wireCap ∧
            circuit.descriptionBits ≤
              thresholdDescriptionCap arity wireCap := by
    intro term
    exact existsNormalizedThresholdAtom normalization
      (sum.legal term.val term.property)
  let circuitFor :
      {term // term ∈ sum.terms} →
        NormalizedThresholdThresholdCircuit arity :=
    fun term => Classical.choose (normalized term)
  have circuitFor_spec (term : {term // term ∈ sum.terms}) :
      (circuitFor term).eval = term.val.2 ∧
        (circuitFor term).wireCount ≤ wireCap ∧
        (circuitFor term).descriptionBits ≤
          thresholdDescriptionCap arity wireCap :=
    Classical.choose_spec (normalized term)
  let canonicalTerms :
      List (LegalCircuitTerm NormalizedThresholdThresholdCircuit arity) :=
    sum.terms.attach.map fun term =>
      { coefficient := term.val.1
        circuit := circuitFor term }
  let description :
      LegalCircuitSumDescription NormalizedThresholdThresholdCircuit :=
    { q := arity
      terms := canonicalTerms }
  have hcanonicalTermsLength :
      canonicalTerms.length = sum.terms.length := by
    simp [canonicalTerms]
  have hcanonicalMass :
      description.coefficientMass =
        sum.terms.foldl (fun total term => total + |term.1|) 0 := by
    simp only [description, LegalCircuitSumDescription.coefficientMass,
      canonicalTerms, List.foldl_map]
    simpa only [List.foldl_map] using
      congrArg
        (fun masses : List ℚ => masses.foldl (· + ·) 0)
        (List.attach_map_val
          (l := sum.terms)
          (f := fun term : ℚ × BoolFunction arity => |term.1|))
  have hcanonicalCoefficients :
      canonicalTerms.map (·.coefficient) =
        sum.terms.map (·.1) := by
    simp only [canonicalTerms, List.map_map]
    exact
      List.attach_map_val
        (l := sum.terms)
        (f := fun term : ℚ × BoolFunction arity => term.1)
  let checked : CheckedLegalCircuitSum
      NormalizedThresholdThresholdCircuit
      NormalizedThresholdThresholdCircuit.wireCount
      NormalizedThresholdThresholdCircuit.descriptionBits
      (thresholdXorLegalSumLimits witness delta copies arity wireCap) :=
    { value := description
      arity_eq := rfl
      terms_le := by
        rw [hcanonicalTermsLength]
        exact hterms
      coefficient_bits_le := by
        intro term hterm
        rcases List.mem_map.mp hterm with
          ⟨sourceTerm, _, rfl⟩
        exact hbits sourceTerm.val sourceTerm.property
      mass_le := by
        rw [hcanonicalMass]
        exact rationalCoefficientMass_le_ceil sum
          (xorAuthorizedCoefficientMass witness delta copies) hmass
      wires_le := by
        intro term hterm
        rcases List.mem_map.mp hterm with
          ⟨sourceTerm, _, rfl⟩
        exact (circuitFor_spec sourceTerm).2.1
      description_le := by
        intro term hterm
        rcases List.mem_map.mp hterm with
          ⟨sourceTerm, _, rfl⟩
        exact (circuitFor_spec sourceTerm).2.2 }
  refine ⟨checked, ?_, ?_⟩
  · simpa only [checked, description] using hcanonicalCoefficients
  · intro input
    change BitInput arity at input
    have foldCorrespondence :
        ∀ (terms : List {term // term ∈ sum.terms}) (initial : ℝ),
          (terms.map fun term =>
              ({ coefficient := term.val.1
                 circuit := circuitFor term } :
                LegalCircuitTerm
                  NormalizedThresholdThresholdCircuit arity)).foldl
                (fun total term =>
                  total + (term.coefficient : ℝ) *
                    bitAsReal (term.circuit.eval input)) initial =
            terms.foldl
              (fun total term =>
                total + (term.val.1 : ℝ) *
                  bitAsReal (term.val.2 input)) initial := by
      intro terms
      induction terms with
      | nil =>
          intro initial
          rfl
      | cons term terms inductionHypothesis =>
          intro initial
          simp only [List.map_cons, List.foldl_cons]
          rw [congrFun (circuitFor_spec term).1 input]
          exact inductionHypothesis _
    change
      canonicalTerms.foldl
          (fun total term =>
            total + (term.coefficient : ℝ) *
              bitAsReal (term.circuit.eval input)) 0 =
        sum.value input
    rw [foldCorrespondence sum.terms.attach 0]
    unfold UnitIntervalCircuitSum.value
    simpa only [List.foldl_map] using
      congrArg
        (fun contributions : List ℝ =>
          contributions.foldl (· + ·) 0)
        (List.attach_map_val
          (l := sum.terms)
          (f := fun term : ℚ × BoolFunction arity =>
            (term.1 : ℝ) * bitAsReal (term.2 input)))

/-- Direct symmetric-mode completeness handoff to the canonical recovery
decoder.  The normalized sum is selected from the conversion theorem above,
not supplied by the caller. -/
noncomputable def symmetricCheckedRecoveryWitness_of_contracts
    (normalization : ThresholdNormalizationContract)
    (witness : XorAmplificationWitness) (delta : ℝ) (copies : ℕ)
    {oracleArity oracleSizeCap sumArity
      symmetricWireCap thresholdWireCap : ℕ}
    (oracle : BooleanCircuit oracleArity)
    (oracleSize_le : oracle.size ≤ oracleSizeCap)
    (sum : UnitIntervalCircuitSum
      symmetricWireFamily sumArity symmetricWireCap)
    (hterms :
      sum.terms.length ≤
        xorAuthorizedTermCap witness delta copies sumArity)
    (hbits :
      sum.coefficientsWithinBitBound
        (xorAuthorizedCoefficientBitCap witness delta sumArity))
    (hmass :
      sum.coefficientMass ≤
        xorAuthorizedCoefficientMass witness delta copies) :
    CheckedRecoveryWitness
      (xorRecoveryWitnessLimits witness delta copies
        oracleArity oracleSizeCap sumArity
        symmetricWireCap thresholdWireCap) :=
  .symmetric oracle oracleSize_le
    (Classical.choose
      (symmetricCheckedLegalCircuitSum_of_contracts
        normalization witness delta copies sum hterms hbits hmass))

/-- Direct threshold-mode completeness handoff.  Support compression and both
normalization layers remain internal to the unique conversion path. -/
noncomputable def thresholdCheckedRecoveryWitness_of_contracts
    (normalization : ThresholdNormalizationContract)
    (witness : XorAmplificationWitness) (delta : ℝ) (copies : ℕ)
    {oracleArity oracleSizeCap sumArity
      symmetricWireCap thresholdWireCap : ℕ}
    (oracle : BooleanCircuit oracleArity)
    (oracleSize_le : oracle.size ≤ oracleSizeCap)
    (sum : UnitIntervalCircuitSum
      thresholdWireFamily sumArity thresholdWireCap)
    (hterms :
      sum.terms.length ≤
        xorAuthorizedTermCap witness delta copies sumArity)
    (hbits :
      sum.coefficientsWithinBitBound
        (xorAuthorizedCoefficientBitCap witness delta sumArity))
    (hmass :
      sum.coefficientMass ≤
        xorAuthorizedCoefficientMass witness delta copies) :
    CheckedRecoveryWitness
      (xorRecoveryWitnessLimits witness delta copies
        oracleArity oracleSizeCap sumArity
        symmetricWireCap thresholdWireCap) :=
  .threshold oracle oracleSize_le
    (Classical.choose
      (thresholdCheckedLegalCircuitSum_of_contracts
        normalization witness delta copies sum hterms hbits hmass))

end NearCubicWires.RecoveryWitnessNormalization
