import Proof.Circuits.CanonicalWitnessCodec
import Proof.Foundations.CircuitRestriction
import Proof.Foundations.PolynomialClock
import Proof.Foundations.PolynomialSchedule

/-!
# Canonical recovery-witness policy

The weak machine may search only one finite syntax class, so its resource
limits must be derived from the source parameters rather than supplied by a
caller.  This module establishes the normalization and description bounds
needed by that policy.  In particular, `THR ∘ THR` circuits are compressed to
their physically retained top support before integer normalization; otherwise
unused zero-weight gates could make the syntax arbitrarily larger than the
wire charge.
-/

namespace NearCubicWires.RecoveryWitnessPolicy

open scoped BigOperators

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.CircuitRestriction
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PolynomialSchedule
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

/-- The elementary binary-length bound used for normalized integer weights. -/
theorem self_le_two_pow (value : ℕ) : value ≤ 2 ^ value := by
  induction value with
  | zero => simp
  | succ value inductionHypothesis =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ value := Nat.one_le_two_pow
      omega

theorem natBitLength_self_pow_le_square (value : ℕ) :
    natBitLength (value ^ value) ≤ value * value + 1 := by
  have hpower : value ^ value ≤ 2 ^ (value * value) := by
    calc
      value ^ value ≤ (2 ^ value) ^ value :=
        Nat.pow_le_pow_left (self_le_two_pow value) value
      _ = 2 ^ (value * value) := (Nat.pow_mul 2 value value).symm
  calc
    natBitLength (value ^ value) ≤
        natBitLength (2 ^ (value * value)) :=
      natBitLength_mono hpower
    _ = value * value + 1 := by
      simp [natBitLength, Nat.log_pow]

theorem intBitLength_le_of_natAbs_le
    {value : ℤ} {bound bits : ℕ}
    (hvalue : value.natAbs ≤ bound)
    (hbits : natBitLength bound ≤ bits) :
    intBitLength value ≤ bits := by
  exact (natBitLength_mono hvalue).trans hbits

/-- Description charge for one support-first gate of the displayed arity. -/
def normalizedGateDescriptionCap (arity : ℕ) : ℕ :=
  (arity + 1) * (arity * arity + 1) + arity

theorem normalizedGate_encodingBits_le
    {arity : ℕ} (gate : NormalizedThresholdGate arity)
    (hparameters : gate.parametersBoundedBy (arity ^ arity)) :
    gate.encodingBits ≤ (arity + 1) * (arity * arity + 1) := by
  classical
  have hbit :
      ∀ value : ℤ, value.natAbs ≤ arity ^ arity →
        intBitLength value ≤ arity * arity + 1 := by
    intro value hvalue
    exact intBitLength_le_of_natAbs_le hvalue
      (natBitLength_self_pow_le_square arity)
  unfold NormalizedThresholdGate.encodingBits
  have hthreshold :
      intBitLength gate.threshold ≤ arity * arity + 1 :=
    hbit gate.threshold hparameters.2
  have hweights :
      (∑ index, intBitLength (gate.weight index)) ≤
        arity * (arity * arity + 1) := by
    simpa using
      (Finset.sum_le_card_nsmul Finset.univ
        (fun index => intBitLength (gate.weight index))
        (arity * arity + 1)
        (fun index _ => hbit (gate.weight index) (hparameters.1 index)))
  calc
    intBitLength gate.threshold +
          ∑ index, intBitLength (gate.weight index) ≤
        (arity * arity + 1) +
          arity * (arity * arity + 1) :=
      Nat.add_le_add hthreshold hweights
    _ = (arity + 1) * (arity * arity + 1) := by ring

theorem supportedGate_descriptionBits_le
    {arity : ℕ} (gate : SupportedNormalizedGate arity)
    (hparameters : gate.gate.parametersBoundedBy (arity ^ arity)) :
    gate.descriptionBits ≤ normalizedGateDescriptionCap arity := by
  exact Nat.add_le_add_right
    (normalizedGate_encodingBits_le gate.gate hparameters) arity

theorem symmetric_bottomCount_le_wireCount
    {arity : ℕ} (circuit : NormalizedSymmetricThresholdCircuit arity) :
    circuit.bottomCount ≤ circuit.wireCount := by
  unfold NormalizedSymmetricThresholdCircuit.wireCount
  calc
    circuit.bottomCount =
        ∑ _index : Fin circuit.bottomCount, 1 := by simp
    _ ≤ ∑ index, ((circuit.bottom index).wireCount + 1) :=
      Finset.sum_le_sum
        (fun _index _ => Nat.le_add_left 1 _)

/-- A uniform syntax cap for normalized `SYM ∘ THR` atoms. -/
def symmetricDescriptionCap (arity wireCap : ℕ) : ℕ :=
  (wireCap + 1) * (normalizedGateDescriptionCap arity + 1)

theorem normalizedSymmetric_descriptionBits_le
    {arity wireCap : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit arity)
    (hwires : circuit.wireCount ≤ wireCap)
    (hparameters :
      ∀ index,
        (circuit.bottom index).gate.parametersBoundedBy (arity ^ arity)) :
    circuit.descriptionBits ≤ symmetricDescriptionCap arity wireCap := by
  have hcount : circuit.bottomCount ≤ wireCap :=
    (symmetric_bottomCount_le_wireCount circuit).trans hwires
  have hsum :
      (∑ index, (circuit.bottom index).descriptionBits) ≤
        circuit.bottomCount * normalizedGateDescriptionCap arity := by
    simpa using
      (Finset.sum_le_card_nsmul Finset.univ
        (fun index => (circuit.bottom index).descriptionBits)
        (normalizedGateDescriptionCap arity)
        (fun index _ =>
          supportedGate_descriptionBits_le
            (circuit.bottom index) (hparameters index)))
  unfold NormalizedSymmetricThresholdCircuit.descriptionBits
    symmetricDescriptionCap
  calc
    circuit.bottomCount + 1 +
          ∑ index, (circuit.bottom index).descriptionBits ≤
        circuit.bottomCount + 1 +
          circuit.bottomCount * normalizedGateDescriptionCap arity :=
      Nat.add_le_add_left hsum _
    _ ≤ (wireCap + 1) * (normalizedGateDescriptionCap arity + 1) := by
      nlinarith

/-! ## Support-first compression for `THR ∘ THR` -/

noncomputable def retainedSourceTop {arity : ℕ}
    (circuit : ThresholdThresholdCircuit arity) :
    Finset (Fin circuit.bottomCount) :=
  Finset.univ.filter fun index => circuit.topWeight index ≠ 0

noncomputable def retainedSourceIndex {arity : ℕ}
    (circuit : ThresholdThresholdCircuit arity) :
    Fin (retainedSourceTop circuit).card ↪o Fin circuit.bottomCount :=
  (retainedSourceTop circuit).orderEmbOfFin rfl

/-- Delete every bottom gate whose top coefficient is zero before any syntax
or normalization bound is measured. -/
noncomputable def compressThresholdCircuit {arity : ℕ}
    (circuit : ThresholdThresholdCircuit arity) :
    ThresholdThresholdCircuit arity where
  bottomCount := (retainedSourceTop circuit).card
  bottom index := circuit.bottom (retainedSourceIndex circuit index)
  topWeight index := circuit.topWeight (retainedSourceIndex circuit index)
  topThreshold := circuit.topThreshold

theorem compressThresholdCircuit_eval
    {arity : ℕ} (circuit : ThresholdThresholdCircuit arity)
    (input : BitInput arity) :
    (compressThresholdCircuit circuit).eval input = circuit.eval input := by
  classical
  unfold ThresholdThresholdCircuit.eval
    compressThresholdCircuit
  apply decide_eq_decide.mpr
  let embedding :
      Fin (retainedSourceTop circuit).card ↪ Fin circuit.bottomCount :=
    (retainedSourceIndex circuit).toEmbedding
  have hmap :
      Finset.map embedding Finset.univ = retainedSourceTop circuit := by
    simp [embedding, retainedSourceIndex]
  have hretained :
      (∑ index : Fin (retainedSourceTop circuit).card,
          circuit.topWeight (embedding index) *
            bitAsReal ((circuit.bottom (embedding index)).eval input)) =
        ∑ index ∈ retainedSourceTop circuit,
          circuit.topWeight index *
            bitAsReal ((circuit.bottom index).eval input) := by
    conv_rhs => rw [← hmap]
    exact
      (Finset.sum_map Finset.univ embedding
        (fun index =>
          circuit.topWeight index *
            bitAsReal ((circuit.bottom index).eval input))).symm
  change
    circuit.topThreshold ≤
        ∑ index : Fin (retainedSourceTop circuit).card,
          circuit.topWeight (embedding index) *
            bitAsReal ((circuit.bottom (embedding index)).eval input) ↔
      circuit.topThreshold ≤
        ∑ index,
          circuit.topWeight index *
            bitAsReal ((circuit.bottom index).eval input)
  have hsupport :
      (∑ index ∈ retainedSourceTop circuit,
          circuit.topWeight index *
            bitAsReal ((circuit.bottom index).eval input)) =
        ∑ index,
          circuit.topWeight index *
            bitAsReal ((circuit.bottom index).eval input) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro index _ hnotRetained
    have hzero : circuit.topWeight index = 0 := by
      simpa [retainedSourceTop] using hnotRetained
    simp [hzero]
  rw [hretained, hsupport]

theorem compressThresholdCircuit_wireCount
    {arity : ℕ} (circuit : ThresholdThresholdCircuit arity) :
    (compressThresholdCircuit circuit).wireCount = circuit.wireCount := by
  classical
  unfold ThresholdThresholdCircuit.wireCount
    compressThresholdCircuit
  let embedding :
      Fin (retainedSourceTop circuit).card ↪ Fin circuit.bottomCount :=
    (retainedSourceIndex circuit).toEmbedding
  have hmap :
      Finset.map embedding Finset.univ = retainedSourceTop circuit := by
    simp [embedding, retainedSourceIndex]
  have hnonzero :
      ∀ index : Fin (retainedSourceTop circuit).card,
        circuit.topWeight (embedding index) ≠ 0 := by
    intro index
    have hmem :
        embedding index ∈ retainedSourceTop circuit := by
      change retainedSourceIndex circuit index ∈ retainedSourceTop circuit
      simp [retainedSourceIndex]
    simpa [retainedSourceTop] using hmem
  have hfilter :
      Finset.univ.filter (fun index =>
        circuit.topWeight (embedding index) ≠ 0) = Finset.univ := by
    exact Finset.filter_eq_self.2 (fun index _ => hnonzero index)
  change
    (∑ index ∈ Finset.univ.filter (fun index =>
        circuit.topWeight (embedding index) ≠ 0),
        ((circuit.bottom (embedding index)).support.card + 1)) =
      ∑ index ∈ retainedSourceTop circuit,
        ((circuit.bottom index).support.card + 1)
  rw [hfilter]
  conv_rhs => rw [← hmap]
  exact
    (Finset.sum_map Finset.univ embedding
      (fun index => (circuit.bottom index).support.card + 1)).symm

theorem compressThresholdCircuit_bottomCount_le_wireCount
    {arity : ℕ} (circuit : ThresholdThresholdCircuit arity) :
    (compressThresholdCircuit circuit).bottomCount ≤ circuit.wireCount := by
  rw [← compressThresholdCircuit_wireCount circuit]
  unfold ThresholdThresholdCircuit.wireCount
  have hnonzero :
      ∀ index : Fin (compressThresholdCircuit circuit).bottomCount,
        (compressThresholdCircuit circuit).topWeight index ≠ 0 := by
    intro index
    have hmem :
        retainedSourceIndex circuit index ∈ retainedSourceTop circuit := by
      simp [retainedSourceIndex]
    simpa [compressThresholdCircuit, retainedSourceTop] using hmem
  have hfilter :
      Finset.univ.filter (fun index =>
        (compressThresholdCircuit circuit).topWeight index ≠ 0) =
          Finset.univ := by
    exact Finset.filter_eq_self.2 (fun index _ => hnonzero index)
  rw [hfilter]
  calc
    (compressThresholdCircuit circuit).bottomCount =
        ∑ _index :
          Fin (compressThresholdCircuit circuit).bottomCount, 1 := by simp
    _ ≤ ∑ index,
        (((compressThresholdCircuit circuit).bottom index).support.card + 1) :=
      Finset.sum_le_sum (fun _index _ => Nat.le_add_left 1 _)

theorem normalizedGateDescriptionCap_mono
    {smaller larger : ℕ} (hle : smaller ≤ larger) :
    normalizedGateDescriptionCap smaller ≤
      normalizedGateDescriptionCap larger := by
  unfold normalizedGateDescriptionCap
  apply Nat.add_le_add
  · exact Nat.mul_le_mul
      (Nat.add_le_add_right hle 1)
      (Nat.add_le_add_right (Nat.mul_le_mul hle hle) 1)
  · exact hle

/-- A uniform syntax cap for a support-compressed normalized `THR ∘ THR`
atom.  Both factors are polynomial in the input arity and physical wire cap. -/
def thresholdDescriptionCap (arity wireCap : ℕ) : ℕ :=
  normalizedGateDescriptionCap wireCap +
    wireCap * normalizedGateDescriptionCap arity

theorem normalizedThreshold_descriptionBits_le
    {arity wireCap : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit arity)
    (hcount : circuit.bottomCount ≤ wireCap)
    (hbottom :
      ∀ index,
        (circuit.bottom index).gate.parametersBoundedBy (arity ^ arity))
    (htop :
      circuit.top.gate.parametersBoundedBy
        (circuit.bottomCount ^ circuit.bottomCount)) :
    circuit.descriptionBits ≤ thresholdDescriptionCap arity wireCap := by
  have htopDescription :
      circuit.top.descriptionBits ≤
        normalizedGateDescriptionCap circuit.bottomCount :=
    supportedGate_descriptionBits_le circuit.top htop
  have htopCap :
      circuit.top.descriptionBits ≤ normalizedGateDescriptionCap wireCap :=
    htopDescription.trans (normalizedGateDescriptionCap_mono hcount)
  have hbottomSum :
      (∑ index, (circuit.bottom index).descriptionBits) ≤
        circuit.bottomCount * normalizedGateDescriptionCap arity := by
    simpa using
      (Finset.sum_le_card_nsmul Finset.univ
        (fun index => (circuit.bottom index).descriptionBits)
        (normalizedGateDescriptionCap arity)
        (fun index _ =>
          supportedGate_descriptionBits_le
            (circuit.bottom index) (hbottom index)))
  unfold NormalizedThresholdThresholdCircuit.descriptionBits
    thresholdDescriptionCap
  exact Nat.add_le_add htopCap
    (hbottomSum.trans
      (Nat.mul_le_mul_right (normalizedGateDescriptionCap arity) hcount))

/-- Compression precedes normalization, so the normalized top description is
bounded by charged top incidences rather than dormant source syntax. -/
theorem existsCompressedNormalizedThresholdCircuit
    (normalization : SourceInterfaces.ThresholdNormalizationContract)
    {arity : ℕ} (source : ThresholdThresholdCircuit arity) :
    ∃ target : NormalizedThresholdThresholdCircuit arity,
      (∀ input, target.eval input = source.eval input) ∧
      target.wireCount = source.wireCount ∧
      target.bottomCount ≤ source.wireCount ∧
      (∀ index,
        (target.bottom index).gate.parametersBoundedBy (arity ^ arity)) ∧
      target.top.gate.parametersBoundedBy
        (target.bottomCount ^ target.bottomCount) := by
  let compressed := compressThresholdCircuit source
  rcases normalizeThresholdCircuit normalization compressed with
    ⟨target, heval, hwires, hbottomCount, hbottom, htop⟩
  refine ⟨target, ?_, ?_, ?_, hbottom, ?_⟩
  · intro input
    rw [heval input, compressThresholdCircuit_eval source input]
  · exact hwires.trans (compressThresholdCircuit_wireCount source)
  · rw [hbottomCount]
    simpa [compressed] using
      compressThresholdCircuit_bottomCount_le_wireCount source
  · have hbound :
        compressed.bottomCount ^ compressed.bottomCount =
          target.bottomCount ^ target.bottomCount := by
      rw [hbottomCount]
    simpa only [hbound] using htop

/-! ## Global weak-witness width -/

/-- Width recurrence for the fixed, zero-terminated records used by the
canonical witness codec.  Variable-size collections continue to use the
balanced codec; this exponential-in-field-count bound is used only for records
whose field count is fixed by the grammar. -/
def taggedListBitBound : List ℕ → ℕ
  | [] => 1
  | fieldBits :: remainingBits =>
      4 * (fieldBits + taggedListBitBound remainingBits)

theorem encodeTaggedList_bits_le (values : List ℕ) :
    natBitLength (encodeTaggedList values) ≤
      taggedListBitBound (values.map natBitLength) := by
  induction values with
  | nil =>
      simp [encodeTaggedList, taggedListBitBound, natBitLength]
  | cons value values inductionHypothesis =>
      let tailCode := encodeTaggedList values
      let payload := Nat.pair value tailCode
      have hpayload :=
        pairCodeBits_le value tailCode
      have houter :=
        pairCodeBits_le 1 payload
      calc
        natBitLength (encodeTaggedList (value :: values)) =
            natBitLength (Nat.pair 1 payload) := by
              simp [encodeTaggedList, payload, tailCode]
        _ ≤ 2 * max (natBitLength 1) (natBitLength payload) :=
          houter
        _ = 2 * natBitLength payload := by
          rw [max_eq_right (by
            norm_num [natBitLength])]
        _ ≤ 4 * max (natBitLength value) (natBitLength tailCode) := by
          calc
            2 * natBitLength payload ≤
                2 * (2 *
                  max (natBitLength value) (natBitLength tailCode)) :=
              Nat.mul_le_mul_left 2 hpayload
            _ = 4 *
                max (natBitLength value) (natBitLength tailCode) := by
              ring
        _ ≤ 4 * (natBitLength value + natBitLength tailCode) := by
          gcongr
          exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
        _ ≤ 4 *
              (natBitLength value +
                taggedListBitBound (values.map natBitLength)) := by
          gcongr
        _ =
            taggedListBitBound
              ((value :: values).map natBitLength) := by
          simp [taggedListBitBound]

/-- Aggregate width rule for the balanced variable-length portions of the
witness grammar.  It depends only on a public element count and one public
per-element width, so callers never supply a bound on an encoded witness. -/
theorem encodeBalancedList_bits_le_of_bounds
    (values : List ℕ) (count atomBits : ℕ)
    (hlength : values.length ≤ count)
    (hatom : ∀ value ∈ values, natBitLength value ≤ atomBits) :
    natBitLength (encodeBalancedList values) ≤
      1 + 2 * count ^ 4 * (count * atomBits + 1) := by
  have hsum :
      (values.map natBitLength).sum ≤ values.length * atomBits := by
    have hsumGeneral :
        ∀ items : List ℕ,
          (∀ value ∈ items, natBitLength value ≤ atomBits) →
            (items.map natBitLength).sum ≤ items.length * atomBits := by
      intro items hitems
      induction items with
      | nil => simp
      | cons value items inductionHypothesis =>
          have hvalue := hitems value (by simp)
          have hremaining :
              ∀ item ∈ items, natBitLength item ≤ atomBits := by
            intro item hitem
            exact hitems item (by simp [hitem])
          calc
            ((value :: items).map natBitLength).sum =
                natBitLength value +
                  (items.map natBitLength).sum := by
              rfl
            _ ≤ atomBits + items.length * atomBits :=
              Nat.add_le_add hvalue (inductionHypothesis hremaining)
            _ = (value :: items).length * atomBits := by
              simp only [List.length_cons, Nat.add_mul, one_mul]
              omega
    exact hsumGeneral values hatom
  have hpower : values.length ^ 4 ≤ count ^ 4 :=
    Nat.pow_le_pow_left hlength 4
  have hatomTotal :
      (values.map natBitLength).sum + 1 ≤ count * atomBits + 1 :=
    Nat.add_le_add_right
      (hsum.trans (Nat.mul_le_mul_right atomBits hlength)) 1
  calc
    natBitLength (encodeBalancedList values) ≤
        1 + 2 * values.length ^ 4 *
          balancedListAtomBits values :=
      balancedListCodeBits_le values
    _ = 1 + 2 * values.length ^ 4 *
          ((values.map natBitLength).sum + 1) := by
      rfl
    _ ≤ 1 + 2 * count ^ 4 * (count * atomBits + 1) := by
      exact Nat.add_le_add_left
        (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hpower) hatomTotal) 1

/-- A canonical natural bounded by `parameter` uses this many bits after
structural binary encoding. -/
def canonicalNatCodeBitBound (parameter : ℕ) : ℕ :=
  encodeNatBitsBound (parameter + 1)

/-- A canonical signed integer with magnitude bit length at most `parameter`
uses this many bits, including its sign/magnitude pairing node. -/
def canonicalIntCodeBitBound (parameter : ℕ) : ℕ :=
  2 * (1 + encodeNatBitsBound parameter)

/-- Uniform width of a balanced list with at most `parameter` atoms, each
using at most `atomBits` bits. -/
def canonicalBalancedCodeBitBound
    (parameter atomBits : ℕ) : ℕ :=
  1 + 2 * parameter ^ 4 * (parameter * atomBits + 1)

private theorem encodeNatBitsBound_mono
    {smaller larger : ℕ} (hle : smaller ≤ larger) :
    encodeNatBitsBound smaller ≤ encodeNatBitsBound larger := by
  unfold encodeNatBitsBound
  gcongr

theorem encodeNat_bits_le_parameter
    {value parameter : ℕ} (hvalue : value ≤ parameter) :
    natBitLength (encodeNat value) ≤ canonicalNatCodeBitBound parameter := by
  have hbits : natBitLength value ≤ parameter + 1 := by
    unfold natBitLength
    exact Nat.add_le_add_right
      ((Nat.log_le_self 2 value).trans hvalue) 1
  exact (encodeNat_bits_le value).trans
    (encodeNatBitsBound_mono hbits)

theorem encodeInt_bits_le_parameter
    {value : ℤ} {parameter : ℕ}
    (hvalue : intBitLength value ≤ parameter) :
    natBitLength (encodeInt value) ≤ canonicalIntCodeBitBound parameter := by
  have hsource :
      natBitLength value.natAbs ≤ parameter := by
    simpa [intBitLength, natBitLength] using hvalue
  have hmagnitude :
      natBitLength (encodeNat value.natAbs) ≤
        encodeNatBitsBound parameter :=
    (encodeNat_bits_le value.natAbs).trans
      (encodeNatBitsBound_mono hsource)
  have hpair :=
    pairCodeBits_le (if value < 0 then 1 else 0)
      (encodeNat value.natAbs)
  calc
    natBitLength (encodeInt value) ≤
        2 * max
          (natBitLength (if value < 0 then 1 else 0))
          (natBitLength (encodeNat value.natAbs)) := by
      simpa [encodeInt] using hpair
    _ ≤ canonicalIntCodeBitBound parameter := by
      unfold canonicalIntCodeBitBound
      have hsign :
          natBitLength (if value < 0 then 1 else 0) ≤ 1 := by
        split <;> rfl
      gcongr
      exact max_le (hsign.trans (Nat.le_add_right _ _))
        (hmagnitude.trans (Nat.le_add_left _ _))

theorem encodeTaggedList_two_bits_le
    {first second firstBits secondBits : ℕ}
    (hfirst : natBitLength first ≤ firstBits)
    (hsecond : natBitLength second ≤ secondBits) :
    natBitLength (encodeTaggedList [first, second]) ≤
      taggedListBitBound [firstBits, secondBits] := by
  calc
    natBitLength (encodeTaggedList [first, second]) ≤
        taggedListBitBound
          ([first, second].map natBitLength) :=
      encodeTaggedList_bits_le _
    _ ≤ taggedListBitBound [firstBits, secondBits] := by
      simp only [List.map_cons, List.map_nil, taggedListBitBound]
      omega

theorem encodeTaggedList_three_bits_le
    {first second third firstBits secondBits thirdBits : ℕ}
    (hfirst : natBitLength first ≤ firstBits)
    (hsecond : natBitLength second ≤ secondBits)
    (hthird : natBitLength third ≤ thirdBits) :
    natBitLength (encodeTaggedList [first, second, third]) ≤
      taggedListBitBound [firstBits, secondBits, thirdBits] := by
  calc
    natBitLength (encodeTaggedList [first, second, third]) ≤
        taggedListBitBound
          ([first, second, third].map natBitLength) :=
      encodeTaggedList_bits_le _
    _ ≤ taggedListBitBound [firstBits, secondBits, thirdBits] := by
      simp only [List.map_cons, List.map_nil, taggedListBitBound]
      omega

theorem encodeTaggedList_four_bits_le
    {first second third fourth firstBits secondBits thirdBits fourthBits : ℕ}
    (hfirst : natBitLength first ≤ firstBits)
    (hsecond : natBitLength second ≤ secondBits)
    (hthird : natBitLength third ≤ thirdBits)
    (hfourth : natBitLength fourth ≤ fourthBits) :
    natBitLength (encodeTaggedList [first, second, third, fourth]) ≤
      taggedListBitBound [firstBits, secondBits, thirdBits, fourthBits] := by
  calc
    natBitLength (encodeTaggedList [first, second, third, fourth]) ≤
        taggedListBitBound
          ([first, second, third, fourth].map natBitLength) :=
      encodeTaggedList_bits_le _
    _ ≤
        taggedListBitBound
          [firstBits, secondBits, thirdBits, fourthBits] := by
      simp only [List.map_cons, List.map_nil, taggedListBitBound]
      omega

def canonicalBooleanNodeCodeBitBound (parameter : ℕ) : ℕ :=
  taggedListBitBound
    [canonicalNatCodeBitBound parameter,
      canonicalNatCodeBitBound parameter,
      canonicalNatCodeBitBound parameter]

def canonicalBooleanCircuitCodeBitBound (parameter : ℕ) : ℕ :=
  taggedListBitBound
    [canonicalBalancedCodeBitBound parameter
        (canonicalBooleanNodeCodeBitBound parameter),
      canonicalNatCodeBitBound parameter]

private theorem encodeBooleanNode_bits_le_parameter
    {arity parameter : ℕ} (node : BooleanNode arity)
    (hparameter : 4 ≤ parameter)
    (harity : arity ≤ parameter)
    (hchildren :
      match node with
      | .const _ => True
      | .input _ => True
      | .not child => child ≤ parameter
      | .and left right => left ≤ parameter ∧ right ≤ parameter
      | .or left right => left ≤ parameter ∧ right ≤ parameter) :
    natBitLength (encodeBooleanNode node) ≤
      canonicalBooleanNodeCodeBitBound parameter := by
  cases node with
  | const value =>
      refine (encodeTaggedList_two_bits_le
        (encodeNat_bits_le_parameter
          (value := 0) (parameter := parameter) (by omega))
        (encodeNat_bits_le_parameter
          (value := value.toNat) (parameter := parameter)
          (by
            cases value with
            | false =>
                change 0 ≤ parameter
                exact Nat.zero_le _
            | true =>
                change 1 ≤ parameter
                omega))).trans ?_
      simp only [canonicalBooleanNodeCodeBitBound, taggedListBitBound]
      omega
  | input index =>
      refine (encodeTaggedList_two_bits_le
        (encodeNat_bits_le_parameter
          (value := 1) (parameter := parameter) (by omega))
        (encodeNat_bits_le_parameter
          (value := index.val) (parameter := parameter)
          (index.isLt.le.trans harity))).trans ?_
      simp only [canonicalBooleanNodeCodeBitBound, taggedListBitBound]
      omega
  | not child =>
      refine (encodeTaggedList_two_bits_le
        (encodeNat_bits_le_parameter
          (value := 2) (parameter := parameter) (by omega))
        (encodeNat_bits_le_parameter
          (value := child) (parameter := parameter) hchildren)).trans ?_
      simp only [canonicalBooleanNodeCodeBitBound, taggedListBitBound]
      omega
  | and left right =>
      exact encodeTaggedList_three_bits_le
        (encodeNat_bits_le_parameter
          (value := 3) (parameter := parameter) (by omega))
        (encodeNat_bits_le_parameter
          (value := left) (parameter := parameter) hchildren.1)
        (encodeNat_bits_le_parameter
          (value := right) (parameter := parameter) hchildren.2)
  | or left right =>
      exact encodeTaggedList_three_bits_le
        (encodeNat_bits_le_parameter
          (value := 4) (parameter := parameter) hparameter)
        (encodeNat_bits_le_parameter
          (value := left) (parameter := parameter) hchildren.1)
        (encodeNat_bits_le_parameter
          (value := right) (parameter := parameter) hchildren.2)

theorem encodeBooleanCircuit_bits_le_parameter
    {arity parameter : ℕ} (circuit : BooleanCircuit arity)
    (hparameter : 4 ≤ parameter)
    (harity : arity ≤ parameter)
    (hsize : circuit.size ≤ parameter) :
    natBitLength (encodeBooleanCircuit circuit) ≤
      canonicalBooleanCircuitCodeBitBound parameter := by
  have hnodes :
      natBitLength
          (encodeBalancedList
            (circuit.nodes.map encodeBooleanNode)) ≤
        canonicalBalancedCodeBitBound parameter
          (canonicalBooleanNodeCodeBitBound parameter) := by
    apply encodeBalancedList_bits_le_of_bounds
    · simpa [BooleanCircuit.size] using hsize
    · intro code hcode
      rcases List.mem_map.mp hcode with ⟨node, hnode, rfl⟩
      rcases List.mem_iff_get.mp hnode with ⟨index, hindex⟩
      have hwellFormed := circuit.wellFormed index
      rw [hindex] at hwellFormed
      apply encodeBooleanNode_bits_le_parameter node hparameter harity
      cases node with
      | const value => trivial
      | input inputIndex => trivial
      | not child =>
          simp only [BooleanNode.WellFormedAt] at hwellFormed
          exact hwellFormed.le.trans
            (index.isLt.le.trans (by
              simpa [BooleanCircuit.size] using hsize))
      | and left right =>
          simp only [BooleanNode.WellFormedAt] at hwellFormed
          constructor
          · exact hwellFormed.1.le.trans
              (index.isLt.le.trans (by
                simpa [BooleanCircuit.size] using hsize))
          · exact hwellFormed.2.le.trans
              (index.isLt.le.trans (by
                simpa [BooleanCircuit.size] using hsize))
      | or left right =>
          simp only [BooleanNode.WellFormedAt] at hwellFormed
          constructor
          · exact hwellFormed.1.le.trans
              (index.isLt.le.trans (by
                simpa [BooleanCircuit.size] using hsize))
          · exact hwellFormed.2.le.trans
              (index.isLt.le.trans (by
                simpa [BooleanCircuit.size] using hsize))
  have houtput :
      natBitLength (encodeNat circuit.output.val) ≤
        canonicalNatCodeBitBound parameter :=
    encodeNat_bits_le_parameter <|
      circuit.output.isLt.le.trans <| by
        simpa [BooleanCircuit.size] using hsize
  exact encodeTaggedList_two_bits_le hnodes houtput

def canonicalSupportedGateCodeBitBound (parameter : ℕ) : ℕ :=
  taggedListBitBound
    [canonicalBalancedCodeBitBound parameter
        (canonicalIntCodeBitBound parameter),
      canonicalIntCodeBitBound parameter,
      canonicalBalancedCodeBitBound parameter 1]

theorem encodeBoolList_bits_le_parameter
    (values : List Bool) (parameter : ℕ)
    (hlength : values.length ≤ parameter) :
    natBitLength (encodeBoolList values) ≤
      canonicalBalancedCodeBitBound parameter 1 := by
  unfold encodeBoolList canonicalBalancedCodeBitBound
  apply encodeBalancedList_bits_le_of_bounds
  · simpa using hlength
  · intro code hcode
    rcases List.mem_map.mp hcode with ⟨value, _, rfl⟩
    cases value <;> rfl

theorem encodeIntList_bits_le_parameter
    (values : List ℤ) (parameter : ℕ)
    (hlength : values.length ≤ parameter)
    (hvalue : ∀ value ∈ values, intBitLength value ≤ parameter) :
    natBitLength (encodeIntList values) ≤
      canonicalBalancedCodeBitBound parameter
        (canonicalIntCodeBitBound parameter) := by
  unfold encodeIntList canonicalBalancedCodeBitBound
  apply encodeBalancedList_bits_le_of_bounds
  · simpa using hlength
  · intro code hcode
    rcases List.mem_map.mp hcode with ⟨value, hmember, rfl⟩
    exact encodeInt_bits_le_parameter (hvalue value hmember)

theorem encodeSupportedNormalizedGate_bits_le_parameter
    {arity parameter : ℕ} (gate : SupportedNormalizedGate arity)
    (harity : arity ≤ parameter)
    (hdescription : gate.descriptionBits ≤ parameter) :
    natBitLength (encodeSupportedNormalizedGate gate) ≤
      canonicalSupportedGateCodeBitBound parameter := by
  have hthreshold :
      intBitLength gate.gate.threshold ≤ parameter := by
    unfold SupportedNormalizedGate.descriptionBits
      NormalizedThresholdGate.encodingBits at hdescription
    omega
  have hweight :
      ∀ index, intBitLength (gate.gate.weight index) ≤ parameter := by
    intro index
    have hsingle :
        intBitLength (gate.gate.weight index) ≤
          ∑ candidate, intBitLength (gate.gate.weight candidate) := by
      exact Finset.single_le_sum
        (fun candidate _ => Nat.zero_le
          (intBitLength (gate.gate.weight candidate)))
        (Finset.mem_univ index)
    unfold SupportedNormalizedGate.descriptionBits
      NormalizedThresholdGate.encodingBits at hdescription
    omega
  have hweights :
      natBitLength
          (encodeIntList (List.ofFn gate.gate.weight)) ≤
        canonicalBalancedCodeBitBound parameter
          (canonicalIntCodeBitBound parameter) := by
    apply encodeIntList_bits_le_parameter
    · simpa using harity
    · intro value hvalue
      rcases List.mem_ofFn.mp hvalue with ⟨index, rfl⟩
      exact hweight index
  have hthresholdCode :
      natBitLength (encodeInt gate.gate.threshold) ≤
        canonicalIntCodeBitBound parameter :=
    encodeInt_bits_le_parameter hthreshold
  have hmembership :
      natBitLength
          (encodeBoolList
            (List.ofFn fun index =>
              decide (index ∈ gate.support))) ≤
        canonicalBalancedCodeBitBound parameter 1 := by
    apply encodeBoolList_bits_le_parameter
    simpa using harity
  exact encodeTaggedList_three_bits_le
    hweights hthresholdCode hmembership

def canonicalSymmetricCircuitCodeBitBound (parameter : ℕ) : ℕ :=
  taggedListBitBound
    [canonicalNatCodeBitBound parameter,
      canonicalNatCodeBitBound parameter,
      canonicalBalancedCodeBitBound parameter
        (canonicalSupportedGateCodeBitBound parameter),
      canonicalBalancedCodeBitBound parameter 1]

def canonicalThresholdCircuitCodeBitBound (parameter : ℕ) : ℕ :=
  taggedListBitBound
    [canonicalNatCodeBitBound parameter,
      canonicalNatCodeBitBound parameter,
      canonicalBalancedCodeBitBound parameter
        (canonicalSupportedGateCodeBitBound parameter),
      canonicalSupportedGateCodeBitBound parameter]

theorem supportedGate_descriptionBits_positive
    {arity : ℕ} (gate : SupportedNormalizedGate arity) :
    1 ≤ gate.descriptionBits := by
  unfold SupportedNormalizedGate.descriptionBits
    NormalizedThresholdGate.encodingBits intBitLength
  omega

theorem encodeNormalizedSymmetricCircuit_bits_le_parameter
    {arity parameter : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit arity)
    (hparameter : 4 ≤ parameter)
    (hdescription : circuit.descriptionBits ≤ parameter) :
    natBitLength (encodeNormalizedSymmetricThresholdCircuit circuit) ≤
      canonicalSymmetricCircuitCodeBitBound parameter := by
  have hcount : circuit.bottomCount ≤ parameter := by
    unfold NormalizedSymmetricThresholdCircuit.descriptionBits at hdescription
    omega
  have hbottomDescription :
      ∀ index, (circuit.bottom index).descriptionBits ≤ parameter := by
    intro index
    have hsingle :
        (circuit.bottom index).descriptionBits ≤
          ∑ candidate, (circuit.bottom candidate).descriptionBits := by
      exact Finset.single_le_sum
        (fun candidate _ => Nat.zero_le
          (circuit.bottom candidate).descriptionBits)
        (Finset.mem_univ index)
    unfold NormalizedSymmetricThresholdCircuit.descriptionBits at hdescription
    omega
  have hfamily :
      natBitLength (encodeNat symmetricCircuitFamilyTag) ≤
        canonicalNatCodeBitBound parameter :=
    encodeNat_bits_le_parameter (by
      unfold symmetricCircuitFamilyTag
      omega)
  have hcountCode :
      natBitLength (encodeNat circuit.bottomCount) ≤
        canonicalNatCodeBitBound parameter :=
    encodeNat_bits_le_parameter hcount
  have hbottom :
      natBitLength
          (encodeBalancedList
            (List.ofFn fun index =>
              encodeSupportedNormalizedGate (circuit.bottom index))) ≤
        canonicalBalancedCodeBitBound parameter
          (canonicalSupportedGateCodeBitBound parameter) := by
    unfold canonicalBalancedCodeBitBound
    apply encodeBalancedList_bits_le_of_bounds
    · simpa using hcount
    · intro code hcode
      rcases List.mem_ofFn.mp hcode with ⟨index, rfl⟩
      have hgateDescription := hbottomDescription index
      exact encodeSupportedNormalizedGate_bits_le_parameter
        (circuit.bottom index)
        (by
          unfold SupportedNormalizedGate.descriptionBits at hgateDescription
          omega)
        hgateDescription
  have htop :
      natBitLength (encodeBoolList (List.ofFn circuit.top)) ≤
        canonicalBalancedCodeBitBound parameter 1 := by
    apply encodeBoolList_bits_le_parameter
    simp only [List.length_ofFn]
    unfold NormalizedSymmetricThresholdCircuit.descriptionBits at hdescription
    omega
  exact encodeTaggedList_four_bits_le
    hfamily hcountCode hbottom htop

theorem encodeNormalizedThresholdCircuit_bits_le_parameter
    {arity parameter : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit arity)
    (hparameter : 4 ≤ parameter)
    (hdescription : circuit.descriptionBits ≤ parameter) :
    natBitLength (encodeNormalizedThresholdThresholdCircuit circuit) ≤
      canonicalThresholdCircuitCodeBitBound parameter := by
  have hcountToSum :
      circuit.bottomCount ≤
        ∑ index, (circuit.bottom index).descriptionBits := by
    calc
      circuit.bottomCount =
          ∑ _index : Fin circuit.bottomCount, 1 := by simp
      _ ≤ ∑ index, (circuit.bottom index).descriptionBits :=
        Finset.sum_le_sum
          (fun index _ => supportedGate_descriptionBits_positive
            (circuit.bottom index))
  have hcount : circuit.bottomCount ≤ parameter := by
    unfold NormalizedThresholdThresholdCircuit.descriptionBits at hdescription
    omega
  have htopDescription :
      circuit.top.descriptionBits ≤ parameter := by
    unfold NormalizedThresholdThresholdCircuit.descriptionBits at hdescription
    omega
  have hbottomDescription :
      ∀ index, (circuit.bottom index).descriptionBits ≤ parameter := by
    intro index
    have hsingle :
        (circuit.bottom index).descriptionBits ≤
          ∑ candidate, (circuit.bottom candidate).descriptionBits := by
      exact Finset.single_le_sum
        (fun candidate _ => Nat.zero_le
          (circuit.bottom candidate).descriptionBits)
        (Finset.mem_univ index)
    unfold NormalizedThresholdThresholdCircuit.descriptionBits at hdescription
    omega
  have hfamily :
      natBitLength (encodeNat thresholdCircuitFamilyTag) ≤
        canonicalNatCodeBitBound parameter :=
    encodeNat_bits_le_parameter (by
      unfold thresholdCircuitFamilyTag
      omega)
  have hcountCode :
      natBitLength (encodeNat circuit.bottomCount) ≤
        canonicalNatCodeBitBound parameter :=
    encodeNat_bits_le_parameter hcount
  have hbottom :
      natBitLength
          (encodeBalancedList
            (List.ofFn fun index =>
              encodeSupportedNormalizedGate (circuit.bottom index))) ≤
        canonicalBalancedCodeBitBound parameter
          (canonicalSupportedGateCodeBitBound parameter) := by
    unfold canonicalBalancedCodeBitBound
    apply encodeBalancedList_bits_le_of_bounds
    · simpa using hcount
    · intro code hcode
      rcases List.mem_ofFn.mp hcode with ⟨index, rfl⟩
      have hgateDescription := hbottomDescription index
      exact encodeSupportedNormalizedGate_bits_le_parameter
        (circuit.bottom index)
        (by
          unfold SupportedNormalizedGate.descriptionBits at hgateDescription
          omega)
        hgateDescription
  have htop :
      natBitLength (encodeSupportedNormalizedGate circuit.top) ≤
        canonicalSupportedGateCodeBitBound parameter :=
    encodeSupportedNormalizedGate_bits_le_parameter
      circuit.top hcount htopDescription
  exact encodeTaggedList_four_bits_le
    hfamily hcountCode hbottom htop

/-- Natural payloads such as rational denominators already carry a binary
length certificate, so they do not need the coarser value-based `+ 1` bound. -/
def canonicalBinaryNatCodeBitBound (parameter : ℕ) : ℕ :=
  encodeNatBitsBound parameter

def canonicalRationalCodeBitBound (parameter : ℕ) : ℕ :=
  taggedListBitBound
    [canonicalIntCodeBitBound parameter,
      canonicalBinaryNatCodeBitBound parameter]

def canonicalLegalTermCodeBitBound
    (parameter circuitBits : ℕ) : ℕ :=
  taggedListBitBound
    [canonicalRationalCodeBitBound parameter, circuitBits]

def canonicalLegalSumCodeBitBound
    (parameter circuitBits : ℕ) : ℕ :=
  taggedListBitBound
    [canonicalNatCodeBitBound parameter,
      canonicalBalancedCodeBitBound parameter
        (canonicalLegalTermCodeBitBound parameter circuitBits)]

theorem encodeNat_bits_le_bit_parameter
    {value parameter : ℕ}
    (hvalue : natBitLength value ≤ parameter) :
    natBitLength (encodeNat value) ≤
      canonicalBinaryNatCodeBitBound parameter :=
  (encodeNat_bits_le value).trans (encodeNatBitsBound_mono hvalue)

theorem encodeCanonicalRational_bits_le_parameter
    (coefficient : ℚ) (parameter : ℕ)
    (hnumerator :
      natBitLength coefficient.num.natAbs ≤ parameter)
    (hdenominator : natBitLength coefficient.den ≤ parameter) :
    natBitLength (encodeCanonicalRational coefficient) ≤
      canonicalRationalCodeBitBound parameter := by
  have hnum :
      natBitLength (encodeInt coefficient.num) ≤
        canonicalIntCodeBitBound parameter := by
    apply encodeInt_bits_le_parameter
    simpa [intBitLength, natBitLength] using hnumerator
  have hden :
      natBitLength (encodeNat coefficient.den) ≤
        canonicalBinaryNatCodeBitBound parameter :=
    encodeNat_bits_le_bit_parameter hdenominator
  exact encodeTaggedList_two_bits_le hnum hden

theorem LegalCircuitTerm.code_bits_le_parameter
    {Circuit : NearCubicWires.SupplierPipeline.CircuitFamily}
    {arity parameter circuitBits : ℕ}
    (codec : CanonicalCircuitCodec Circuit)
    (term : LegalCircuitTerm Circuit arity)
    (hnumerator :
      natBitLength term.coefficient.num.natAbs ≤ parameter)
    (hdenominator :
      natBitLength term.coefficient.den ≤ parameter)
    (hcircuit :
      natBitLength (codec.encode term.circuit) ≤ circuitBits) :
    natBitLength (term.code codec) ≤
      canonicalLegalTermCodeBitBound parameter circuitBits := by
  exact encodeTaggedList_two_bits_le
    (encodeCanonicalRational_bits_le_parameter
      term.coefficient parameter hnumerator hdenominator)
    hcircuit

theorem CheckedLegalCircuitSum.code_bits_le_parameter
    {Circuit : NearCubicWires.SupplierPipeline.CircuitFamily}
    {wires description : {arity : ℕ} → Circuit arity → ℕ}
    {limits : LegalSumLimits} {parameter circuitBits : ℕ}
    (codec : CanonicalCircuitCodec Circuit)
    (checked :
      CheckedLegalCircuitSum Circuit wires description limits)
    (harity : limits.expectedArity ≤ parameter)
    (htermCap : limits.termCap ≤ parameter)
    (hcoefficientCap : limits.coefficientBitCap ≤ parameter)
    (hcircuit :
      ∀ term ∈ checked.value.terms,
        natBitLength (codec.encode term.circuit) ≤ circuitBits) :
    natBitLength (checked.code codec) ≤
      canonicalLegalSumCodeBitBound parameter circuitBits := by
  have hq : checked.value.q ≤ parameter := by
    rw [checked.arity_eq]
    exact harity
  have hqCode :
      natBitLength (encodeNat checked.value.q) ≤
        canonicalNatCodeBitBound parameter :=
    encodeNat_bits_le_parameter hq
  have hterms :
      natBitLength
          (encodeBalancedList
            (checked.value.terms.map (·.code codec))) ≤
        canonicalBalancedCodeBitBound parameter
          (canonicalLegalTermCodeBitBound parameter circuitBits) := by
    unfold canonicalBalancedCodeBitBound
    apply encodeBalancedList_bits_le_of_bounds
    · simpa only [List.length_map] using
        checked.terms_le.trans htermCap
    · intro code hcode
      rcases List.mem_map.mp hcode with ⟨term, hterm, rfl⟩
      have hcoefficient := checked.coefficient_bits_le term hterm
      exact LegalCircuitTerm.code_bits_le_parameter codec term
        (hcoefficient.1.trans hcoefficientCap)
        (hcoefficient.2.trans hcoefficientCap)
        (hcircuit term hterm)
  exact encodeTaggedList_two_bits_le hqCode hterms

/-- One public parameter dominates every natural field that can affect the
shape of either checked witness constructor.  The rational mass cap is a
semantic validity check; numerator and denominator syntax is already charged
by `coefficientBitCap`. -/
def recoveryWitnessCodeParameter (limits : RecoveryWitnessLimits) : ℕ :=
  8 +
    limits.oracleArity +
    limits.oracleSizeCap +
    limits.sumArity +
    limits.symmetric.termCap +
    limits.symmetric.coefficientBitCap +
    limits.symmetric.wireCap +
    limits.symmetric.descriptionCap +
    limits.threshold.termCap +
    limits.threshold.coefficientBitCap +
    limits.threshold.wireCap +
    limits.threshold.descriptionCap

def recoveryWitnessCodeBitBound (limits : RecoveryWitnessLimits) : ℕ :=
  let parameter := recoveryWitnessCodeParameter limits
  taggedListBitBound
    [canonicalNatCodeBitBound parameter,
      canonicalBooleanCircuitCodeBitBound parameter,
      max
        (canonicalLegalSumCodeBitBound parameter
          (canonicalSymmetricCircuitCodeBitBound parameter))
        (canonicalLegalSumCodeBitBound parameter
          (canonicalThresholdCircuitCodeBitBound parameter))]

private theorem taggedListBitBound_two_polynomiallyBounded
    {first second : ℕ → ℕ}
    (hfirst : PolynomiallyBounded first)
    (hsecond : PolynomiallyBounded second) :
    PolynomiallyBounded
      (fun parameter => taggedListBitBound
        [first parameter, second parameter]) := by
  have hone := polynomiallyBounded_constant 1
  have hfour := polynomiallyBounded_constant 4
  have htail := polynomiallyBounded_mul hfour
    (polynomiallyBounded_add hsecond hone)
  simpa only [taggedListBitBound] using
    polynomiallyBounded_mul hfour
      (polynomiallyBounded_add hfirst htail)

private theorem taggedListBitBound_three_polynomiallyBounded
    {first second third : ℕ → ℕ}
    (hfirst : PolynomiallyBounded first)
    (hsecond : PolynomiallyBounded second)
    (hthird : PolynomiallyBounded third) :
    PolynomiallyBounded
      (fun parameter => taggedListBitBound
        [first parameter, second parameter, third parameter]) := by
  have hone := polynomiallyBounded_constant 1
  have hfour := polynomiallyBounded_constant 4
  have hthirdTail := polynomiallyBounded_mul hfour
    (polynomiallyBounded_add hthird hone)
  have hsecondTail := polynomiallyBounded_mul hfour
    (polynomiallyBounded_add hsecond hthirdTail)
  simpa only [taggedListBitBound] using
    polynomiallyBounded_mul hfour
      (polynomiallyBounded_add hfirst hsecondTail)

private theorem taggedListBitBound_four_polynomiallyBounded
    {first second third fourth : ℕ → ℕ}
    (hfirst : PolynomiallyBounded first)
    (hsecond : PolynomiallyBounded second)
    (hthird : PolynomiallyBounded third)
    (hfourth : PolynomiallyBounded fourth) :
    PolynomiallyBounded
      (fun parameter => taggedListBitBound
        [first parameter, second parameter, third parameter,
          fourth parameter]) := by
  have hone := polynomiallyBounded_constant 1
  have hfour := polynomiallyBounded_constant 4
  have hfourthTail := polynomiallyBounded_mul hfour
    (polynomiallyBounded_add hfourth hone)
  have hthirdTail := polynomiallyBounded_mul hfour
    (polynomiallyBounded_add hthird hfourthTail)
  have hsecondTail := polynomiallyBounded_mul hfour
    (polynomiallyBounded_add hsecond hthirdTail)
  simpa only [taggedListBitBound] using
    polynomiallyBounded_mul hfour
      (polynomiallyBounded_add hfirst hsecondTail)

private theorem canonicalBalancedCodeBitBound_polynomiallyBounded
    {atomBits : ℕ → ℕ}
    (hatomBits : PolynomiallyBounded atomBits) :
    PolynomiallyBounded
      (fun parameter =>
        canonicalBalancedCodeBitBound parameter
          (atomBits parameter)) := by
  have hparameter := polynomiallyBounded_id
  have hone := polynomiallyBounded_constant 1
  have htwo := polynomiallyBounded_constant 2
  have hpower := polynomiallyBounded_pow hparameter 4
  have hatoms := polynomiallyBounded_add
    (polynomiallyBounded_mul hparameter hatomBits) hone
  have hproduct := polynomiallyBounded_mul
    (polynomiallyBounded_mul htwo hpower) hatoms
  simpa only [canonicalBalancedCodeBitBound] using
    polynomiallyBounded_add hone hproduct

private theorem encodeNatBitsBound_polynomiallyBounded :
    PolynomiallyBounded encodeNatBitsBound := by
  change PolynomiallyBounded
    (fun parameter => encodeNatBitsBound parameter)
  have hparameter := polynomiallyBounded_id
  have hone := polynomiallyBounded_constant 1
  have htwo := polynomiallyBounded_constant 2
  have hpower := polynomiallyBounded_pow hparameter 4
  have hproduct := polynomiallyBounded_mul
    (polynomiallyBounded_mul htwo hpower)
    (polynomiallyBounded_add hparameter hone)
  simpa only [encodeNatBitsBound] using
    polynomiallyBounded_add hone hproduct

private theorem recoveryWitnessCodeBitBound_parameter_polynomiallyBounded :
    PolynomiallyBounded
      (fun parameter =>
        taggedListBitBound
          [canonicalNatCodeBitBound parameter,
            canonicalBooleanCircuitCodeBitBound parameter,
            max
              (canonicalLegalSumCodeBitBound parameter
                (canonicalSymmetricCircuitCodeBitBound parameter))
              (canonicalLegalSumCodeBitBound parameter
                (canonicalThresholdCircuitCodeBitBound parameter))]) := by
  have hparameter := polynomiallyBounded_id
  have hone := polynomiallyBounded_constant 1
  have hnat :
      PolynomiallyBounded canonicalNatCodeBitBound := by
    change PolynomiallyBounded
      (fun parameter => canonicalNatCodeBitBound parameter)
    simpa only [canonicalNatCodeBitBound] using
      polynomiallyBounded_comp encodeNatBitsBound_polynomiallyBounded
        (polynomiallyBounded_add hparameter hone)
  have hint :
      PolynomiallyBounded canonicalIntCodeBitBound := by
    change PolynomiallyBounded
      (fun parameter => canonicalIntCodeBitBound parameter)
    have htwo := polynomiallyBounded_constant 2
    simpa only [canonicalIntCodeBitBound] using
      polynomiallyBounded_mul htwo
        (polynomiallyBounded_add hone
          encodeNatBitsBound_polynomiallyBounded)
  have hnode :
      PolynomiallyBounded canonicalBooleanNodeCodeBitBound := by
    change PolynomiallyBounded
      (fun parameter => canonicalBooleanNodeCodeBitBound parameter)
    simpa only [canonicalBooleanNodeCodeBitBound] using
      taggedListBitBound_three_polynomiallyBounded hnat hnat hnat
  have hboolean :
      PolynomiallyBounded canonicalBooleanCircuitCodeBitBound := by
    change PolynomiallyBounded
      (fun parameter => canonicalBooleanCircuitCodeBitBound parameter)
    simpa only [canonicalBooleanCircuitCodeBitBound] using
      taggedListBitBound_two_polynomiallyBounded
        (canonicalBalancedCodeBitBound_polynomiallyBounded hnode) hnat
  have hgate :
      PolynomiallyBounded canonicalSupportedGateCodeBitBound := by
    change PolynomiallyBounded
      (fun parameter => canonicalSupportedGateCodeBitBound parameter)
    simpa only [canonicalSupportedGateCodeBitBound] using
      taggedListBitBound_three_polynomiallyBounded
        (canonicalBalancedCodeBitBound_polynomiallyBounded hint)
        hint
        (canonicalBalancedCodeBitBound_polynomiallyBounded
          (polynomiallyBounded_constant 1))
  have hsymmetric :
      PolynomiallyBounded canonicalSymmetricCircuitCodeBitBound := by
    change PolynomiallyBounded
      (fun parameter => canonicalSymmetricCircuitCodeBitBound parameter)
    simpa only [canonicalSymmetricCircuitCodeBitBound] using
      taggedListBitBound_four_polynomiallyBounded hnat hnat
        (canonicalBalancedCodeBitBound_polynomiallyBounded hgate)
        (canonicalBalancedCodeBitBound_polynomiallyBounded
          (polynomiallyBounded_constant 1))
  have hthreshold :
      PolynomiallyBounded canonicalThresholdCircuitCodeBitBound := by
    change PolynomiallyBounded
      (fun parameter => canonicalThresholdCircuitCodeBitBound parameter)
    simpa only [canonicalThresholdCircuitCodeBitBound] using
      taggedListBitBound_four_polynomiallyBounded hnat hnat
        (canonicalBalancedCodeBitBound_polynomiallyBounded hgate) hgate
  have hrational :
      PolynomiallyBounded canonicalRationalCodeBitBound := by
    change PolynomiallyBounded
      (fun parameter => canonicalRationalCodeBitBound parameter)
    simpa only [canonicalRationalCodeBitBound,
      canonicalBinaryNatCodeBitBound] using
      taggedListBitBound_two_polynomiallyBounded hint
        encodeNatBitsBound_polynomiallyBounded
  have hlegalTerm
      (circuitBits : ℕ → ℕ)
      (hcircuitBits : PolynomiallyBounded circuitBits) :
      PolynomiallyBounded
        (fun parameter =>
          canonicalLegalTermCodeBitBound parameter
            (circuitBits parameter)) := by
    simpa only [canonicalLegalTermCodeBitBound] using
      taggedListBitBound_two_polynomiallyBounded
        hrational hcircuitBits
  have hlegalSum
      (circuitBits : ℕ → ℕ)
      (hcircuitBits : PolynomiallyBounded circuitBits) :
      PolynomiallyBounded
        (fun parameter =>
          canonicalLegalSumCodeBitBound parameter
            (circuitBits parameter)) := by
    simpa only [canonicalLegalSumCodeBitBound] using
      taggedListBitBound_two_polynomiallyBounded hnat
        (canonicalBalancedCodeBitBound_polynomiallyBounded
          (hlegalTerm circuitBits hcircuitBits))
  exact taggedListBitBound_three_polynomiallyBounded hnat hboolean
    (polynomiallyBounded_max
      (hlegalSum canonicalSymmetricCircuitCodeBitBound hsymmetric)
      (hlegalSum canonicalThresholdCircuitCodeBitBound hthreshold))

/-- Once the public schedule fields are polynomial, the complete canonical
witness grammar is polynomial too; no witness-dependent capacity premise is
introduced. -/
theorem recoveryWitnessCodeBitBound_polynomiallyBounded
    (limits : ℕ → RecoveryWitnessLimits)
    (hparameter :
      PolynomiallyBounded
        (fun sourceIndex =>
          recoveryWitnessCodeParameter (limits sourceIndex))) :
    PolynomiallyBounded
      (fun sourceIndex =>
        recoveryWitnessCodeBitBound (limits sourceIndex)) := by
  simpa only [recoveryWitnessCodeBitBound] using
    polynomiallyBounded_comp
      recoveryWitnessCodeBitBound_parameter_polynomiallyBounded hparameter

/-- Fieldwise schedule closure for the single public syntax parameter.  These
are exactly the natural fields consumed by `recoveryWitnessCodeParameter`; the
rational mass caps are semantic checks whose syntax is already charged by the
coefficient-bit fields. -/
theorem recoveryWitnessCodeParameter_polynomiallyBounded
    (limits : ℕ → RecoveryWitnessLimits)
    (horacleArity :
      PolynomiallyBounded (fun n => (limits n).oracleArity))
    (horacleSize :
      PolynomiallyBounded (fun n => (limits n).oracleSizeCap))
    (hsumArity :
      PolynomiallyBounded (fun n => (limits n).sumArity))
    (hsymmetricTerm :
      PolynomiallyBounded (fun n => (limits n).symmetric.termCap))
    (hsymmetricCoefficient :
      PolynomiallyBounded
        (fun n => (limits n).symmetric.coefficientBitCap))
    (hsymmetricWire :
      PolynomiallyBounded (fun n => (limits n).symmetric.wireCap))
    (hsymmetricDescription :
      PolynomiallyBounded
        (fun n => (limits n).symmetric.descriptionCap))
    (hthresholdTerm :
      PolynomiallyBounded (fun n => (limits n).threshold.termCap))
    (hthresholdCoefficient :
      PolynomiallyBounded
        (fun n => (limits n).threshold.coefficientBitCap))
    (hthresholdWire :
      PolynomiallyBounded (fun n => (limits n).threshold.wireCap))
    (hthresholdDescription :
      PolynomiallyBounded
        (fun n => (limits n).threshold.descriptionCap)) :
    PolynomiallyBounded
      (fun n => recoveryWitnessCodeParameter (limits n)) := by
  have h := polynomiallyBounded_constant 8
  have h := polynomiallyBounded_add h horacleArity
  have h := polynomiallyBounded_add h horacleSize
  have h := polynomiallyBounded_add h hsumArity
  have h := polynomiallyBounded_add h hsymmetricTerm
  have h := polynomiallyBounded_add h hsymmetricCoefficient
  have h := polynomiallyBounded_add h hsymmetricWire
  have h := polynomiallyBounded_add h hsymmetricDescription
  have h := polynomiallyBounded_add h hthresholdTerm
  have h := polynomiallyBounded_add h hthresholdCoefficient
  have h := polynomiallyBounded_add h hthresholdWire
  have h := polynomiallyBounded_add h hthresholdDescription
  simpa only [recoveryWitnessCodeParameter] using h

theorem taggedListBitBound_three_mono_third
    {first second smaller larger : ℕ} (hle : smaller ≤ larger) :
    taggedListBitBound [first, second, smaller] ≤
      taggedListBitBound [first, second, larger] := by
  simp only [taggedListBitBound]
  omega

theorem recoveryWitnessCodeParameter_bounds
    (limits : RecoveryWitnessLimits) :
    let parameter := recoveryWitnessCodeParameter limits
    4 ≤ parameter ∧
      limits.oracleArity ≤ parameter ∧
      limits.oracleSizeCap ≤ parameter ∧
      limits.sumArity ≤ parameter ∧
      limits.symmetric.termCap ≤ parameter ∧
      limits.symmetric.coefficientBitCap ≤ parameter ∧
      limits.symmetric.descriptionCap ≤ parameter ∧
      limits.threshold.termCap ≤ parameter ∧
      limits.threshold.coefficientBitCap ≤ parameter ∧
      limits.threshold.descriptionCap ≤ parameter := by
  dsimp only
  unfold recoveryWitnessCodeParameter
  omega

set_option maxHeartbeats 1000000 in
-- Dependent circuit-family indices make this specialization elaboration-heavy.
theorem symmetricCheckedLegalCircuitSum_code_bits_le
    {limits : RecoveryWitnessLimits}
    (sum : CheckedLegalCircuitSum
      NormalizedSymmetricThresholdCircuit
      NormalizedSymmetricThresholdCircuit.wireCount
      NormalizedSymmetricThresholdCircuit.descriptionBits
      limits.symmetric) :
    let parameter := recoveryWitnessCodeParameter limits
    natBitLength (sum.code symmetricCircuitCodec) ≤
      canonicalLegalSumCodeBitBound parameter
        (canonicalSymmetricCircuitCodeBitBound parameter) := by
  let parameter := recoveryWitnessCodeParameter limits
  rcases recoveryWitnessCodeParameter_bounds limits with
    ⟨hparameter, horacleArity, horacleSize, hsumArity,
      hsymmetricTerm, hsymmetricCoefficient, hsymmetricDescription,
      hthresholdTerm, hthresholdCoefficient, hthresholdDescription⟩
  have hsymmetricArity :
      limits.symmetric.expectedArity ≤ parameter :=
    limits.symmetricArity.le.trans hsumArity
  apply CheckedLegalCircuitSum.code_bits_le_parameter
    symmetricCircuitCodec sum
  · exact hsymmetricArity
  · exact hsymmetricTerm
  · exact hsymmetricCoefficient
  · intro term hterm
    exact encodeNormalizedSymmetricCircuit_bits_le_parameter
      term.circuit hparameter
      ((sum.description_le term hterm).trans hsymmetricDescription)

@[simp] theorem thresholdCircuitCodec_encode_eq
    {arity : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit arity) :
    CanonicalCircuitCodec.encode
        (Circuit := NormalizedThresholdThresholdCircuit)
        thresholdCircuitCodec circuit =
      encodeNormalizedThresholdThresholdCircuit circuit := by
  unfold thresholdCircuitCodec
  simp only

theorem thresholdLegalCircuitTerm_code_bits_le
    {arity parameter : ℕ}
    (term : LegalCircuitTerm
      NormalizedThresholdThresholdCircuit arity)
    (hparameter : 4 ≤ parameter)
    (hnumerator :
      natBitLength term.coefficient.num.natAbs ≤ parameter)
    (hdenominator :
      natBitLength term.coefficient.den ≤ parameter)
    (hdescription :
      term.circuit.descriptionBits ≤ parameter) :
    natBitLength (term.code thresholdCircuitCodec) ≤
      canonicalLegalTermCodeBitBound parameter
        (canonicalThresholdCircuitCodeBitBound parameter) := by
  rw [LegalCircuitTerm.code, thresholdCircuitCodec_encode_eq]
  have hcoefficient :
      natBitLength
          (encodeCanonicalRational term.coefficient) ≤
        canonicalRationalCodeBitBound parameter :=
    encodeCanonicalRational_bits_le_parameter
      term.coefficient parameter hnumerator hdenominator
  have hcircuit :
      natBitLength
          (encodeNormalizedThresholdThresholdCircuit term.circuit) ≤
        canonicalThresholdCircuitCodeBitBound parameter :=
    encodeNormalizedThresholdCircuit_bits_le_parameter
      term.circuit hparameter hdescription
  exact encodeTaggedList_two_bits_le hcoefficient hcircuit

/-- The checked threshold sum uses the compiled term specialization above;
the balanced occurrence list itself remains within the default proof budget. -/
theorem thresholdCheckedLegalCircuitSum_code_bits_le
    {limits : RecoveryWitnessLimits}
    (sum : CheckedLegalCircuitSum
      NormalizedThresholdThresholdCircuit
      NormalizedThresholdThresholdCircuit.wireCount
      NormalizedThresholdThresholdCircuit.descriptionBits
      limits.threshold) :
    let parameter := recoveryWitnessCodeParameter limits
    natBitLength (sum.code thresholdCircuitCodec) ≤
      canonicalLegalSumCodeBitBound parameter
        (canonicalThresholdCircuitCodeBitBound parameter) := by
  let parameter := recoveryWitnessCodeParameter limits
  rcases recoveryWitnessCodeParameter_bounds limits with
    ⟨hparameter, _, _, hsumArity,
      _, _, _,
      hthresholdTerm, hthresholdCoefficient, hthresholdDescription⟩
  have hq : sum.value.q ≤ parameter :=
    sum.arity_eq.le.trans
      (limits.thresholdArity.le.trans hsumArity)
  have hqCode :
      natBitLength (encodeNat sum.value.q) ≤
        canonicalNatCodeBitBound parameter :=
    encodeNat_bits_le_parameter hq
  have hterms :
      natBitLength
          (encodeBalancedList
            (sum.value.terms.map (·.code thresholdCircuitCodec))) ≤
        canonicalBalancedCodeBitBound parameter
          (canonicalLegalTermCodeBitBound parameter
            (canonicalThresholdCircuitCodeBitBound parameter)) := by
    unfold canonicalBalancedCodeBitBound
    apply encodeBalancedList_bits_le_of_bounds
    · simpa only [List.length_map] using
        sum.terms_le.trans hthresholdTerm
    · intro code hcode
      rcases List.mem_map.mp hcode with ⟨term, hterm, rfl⟩
      have hcoefficient := sum.coefficient_bits_le term hterm
      exact thresholdLegalCircuitTerm_code_bits_le term hparameter
        (hcoefficient.1.trans hthresholdCoefficient)
        (hcoefficient.2.trans hthresholdCoefficient)
        ((sum.description_le term hterm).trans hthresholdDescription)
  exact encodeTaggedList_two_bits_le hqCode hterms

private theorem symmetricRecoveryWitness_code_bits_le
    {limits : RecoveryWitnessLimits}
    (oracle : BooleanCircuit limits.oracleArity)
    (horacle : oracle.size ≤ limits.oracleSizeCap)
    (sum : CheckedLegalCircuitSum
      NormalizedSymmetricThresholdCircuit
      NormalizedSymmetricThresholdCircuit.wireCount
      NormalizedSymmetricThresholdCircuit.descriptionBits
      limits.symmetric) :
    natBitLength
        (CheckedRecoveryWitness.symmetric oracle horacle sum).code ≤
      recoveryWitnessCodeBitBound limits := by
  let parameter := recoveryWitnessCodeParameter limits
  rcases recoveryWitnessCodeParameter_bounds limits with
    ⟨hparameter, horacleArity, horacleSize, hsumArity,
      hsymmetricTerm, hsymmetricCoefficient, hsymmetricDescription,
      hthresholdTerm, hthresholdCoefficient, hthresholdDescription⟩
  have hmode :
      natBitLength (encodeNat 0) ≤
        canonicalNatCodeBitBound parameter :=
    encodeNat_bits_le_parameter (Nat.zero_le _)
  have horacleCode :
      natBitLength (encodeBooleanCircuit oracle) ≤
        canonicalBooleanCircuitCodeBitBound parameter :=
    encodeBooleanCircuit_bits_le_parameter oracle hparameter
      horacleArity (horacle.trans horacleSize)
  have hsumCode :=
    symmetricCheckedLegalCircuitSum_code_bits_le sum
  exact (encodeTaggedList_three_bits_le
    hmode horacleCode hsumCode).trans <| by
      unfold recoveryWitnessCodeBitBound
      exact taggedListBitBound_three_mono_third
        (le_max_left _ _)

private theorem thresholdRecoveryWitness_code_bits_le
    {limits : RecoveryWitnessLimits}
    (oracle : BooleanCircuit limits.oracleArity)
    (horacle : oracle.size ≤ limits.oracleSizeCap)
    (sum : CheckedLegalCircuitSum
      NormalizedThresholdThresholdCircuit
      NormalizedThresholdThresholdCircuit.wireCount
      NormalizedThresholdThresholdCircuit.descriptionBits
      limits.threshold) :
    natBitLength
        (CheckedRecoveryWitness.threshold oracle horacle sum).code ≤
      recoveryWitnessCodeBitBound limits := by
  let parameter := recoveryWitnessCodeParameter limits
  rcases recoveryWitnessCodeParameter_bounds limits with
    ⟨hparameter, horacleArity, horacleSize, hsumArity,
      hsymmetricTerm, hsymmetricCoefficient, hsymmetricDescription,
      hthresholdTerm, hthresholdCoefficient, hthresholdDescription⟩
  have hmode :
      natBitLength (encodeNat 1) ≤
        canonicalNatCodeBitBound parameter :=
    encodeNat_bits_le_parameter (by omega)
  have horacleCode :
      natBitLength (encodeBooleanCircuit oracle) ≤
        canonicalBooleanCircuitCodeBitBound parameter :=
    encodeBooleanCircuit_bits_le_parameter oracle hparameter
      horacleArity (horacle.trans horacleSize)
  have hsumCode :=
    thresholdCheckedLegalCircuitSum_code_bits_le sum
  exact (encodeTaggedList_three_bits_le
    hmode horacleCode hsumCode).trans <| by
      unfold recoveryWitnessCodeBitBound
      exact taggedListBitBound_three_mono_third
        (le_max_right _ _)

theorem CheckedRecoveryWitness.code_bits_le
    {limits : RecoveryWitnessLimits}
    (witness : CheckedRecoveryWitness limits) :
    natBitLength witness.code ≤ recoveryWitnessCodeBitBound limits := by
  cases witness with
  | symmetric oracle horacle sum =>
      exact symmetricRecoveryWitness_code_bits_le oracle horacle sum
  | threshold oracle horacle sum =>
      exact thresholdRecoveryWitness_code_bits_le oracle horacle sum

/-- Four-bit right-shift capacity is globally admissible for the published
one-tenth witness-width requirement, including every small input length. -/
theorem recoveryWitnessSixteenth_le_tenth (inputLength : ℕ) :
    inputLength / 16 ≤ inputLength / 10 :=
  Nat.div_le_div_left (by omega) (by omega)

end NearCubicWires.RecoveryWitnessPolicy
