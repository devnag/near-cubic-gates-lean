import Proof.Foundations.CircuitRestriction
import Proof.Circuits.CanonicalWitnessCodec
import Proof.Foundations.SupplierPipeline

/-!
# Canonical occurrence restrictions for normalized supplier atoms

The componentwise verifier guesses atoms on the full occurrence-table domain
and then fixes the clause-address/position suffix before invoking a Fourfold
supplier.  This module performs that operation inside the normalized integer
circuit families.  Fixed coordinates are absorbed into bottom thresholds;
top gates are unchanged, and retained physical wire count cannot increase.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.ComponentwiseCircuitRestriction

open NearCubicWires
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.CircuitRestriction
open NearCubicWires.RecoveryPipeline
open NearCubicWires.SupplierPipeline
open NearCubicWires.ThresholdCompiler

theorem sum_split_int {core target : ℕ} (hcore : core ≤ target)
    (value : Fin target → ℤ) :
    (∑ index : Fin target, value index) =
      (∑ index : Fin core, value (coreIndex hcore index)) +
      ∑ index : Fin (target - core), value (paddingIndex hcore index) := by
  have hsum := Equiv.sum_comp (finSplitEquiv hcore) value
  simpa [coreIndex, paddingIndex] using hsum.symm

/-- Absorb one fixed suffix assignment into an integer threshold gate. -/
def restrictNormalizedThresholdGate {core target : ℕ}
    (gate : NormalizedThresholdGate target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) : NormalizedThresholdGate core where
  weight index := gate.weight (coreIndex hcore index)
  threshold := gate.threshold -
    ∑ index, gate.weight (paddingIndex hcore index) * bitInt (padding index)

theorem restrictNormalizedThresholdGate_eval {core target : ℕ}
    (gate : NormalizedThresholdGate target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) (input : BitInput core) :
    (restrictNormalizedThresholdGate gate hcore padding).eval input =
      gate.eval (fun index =>
        Sum.elim input padding ((finSplitEquiv hcore).symm index)) := by
  let combined : BitInput target := fun index =>
    Sum.elim input padding ((finSplitEquiv hcore).symm index)
  have hcoreValue (index : Fin core) :
      combined (coreIndex hcore index) = input index := by
    simp [combined, coreIndex]
  have hpaddingValue (index : Fin (target - core)) :
      combined (paddingIndex hcore index) = padding index := by
    simp [combined, paddingIndex]
  have hsum :
      (∑ index : Fin target,
          gate.weight index * bitInt (combined index)) =
        (∑ index : Fin core,
          gate.weight (coreIndex hcore index) * bitInt (input index)) +
        ∑ index : Fin (target - core),
          gate.weight (paddingIndex hcore index) *
            bitInt (padding index) := by
    rw [sum_split_int hcore]
    congr 1
    · apply Finset.sum_congr rfl
      intro index _
      rw [hcoreValue]
    · apply Finset.sum_congr rfl
      intro index _
      rw [hpaddingValue]
  unfold NormalizedThresholdGate.eval
  apply decide_eq_decide.mpr
  change
    gate.threshold -
          (∑ index : Fin (target - core),
            gate.weight (paddingIndex hcore index) *
              bitInt (padding index)) ≤
        (∑ index : Fin core,
          gate.weight (coreIndex hcore index) * bitInt (input index)) ↔
      gate.threshold ≤
        ∑ index : Fin target,
          gate.weight index * bitInt (combined index)
  rw [hsum]
  omega

/-- Parameter growth caused by absorbing a fixed suffix.  The linear factor
is charged to the public source arity, never to a guessed assignment. -/
def restrictedParameterBound (target bound : ℕ) : ℕ :=
  (target + 1) * bound

theorem restrictNormalizedThresholdGate_parametersBoundedBy
    {core target bound : ℕ}
    (gate : NormalizedThresholdGate target) (hcore : core ≤ target)
    (padding : BitInput (target - core))
    (hparameters : gate.parametersBoundedBy bound) :
    (restrictNormalizedThresholdGate gate hcore padding).parametersBoundedBy
      (restrictedParameterBound target bound) := by
  have hterm :
      ∀ index : Fin (target - core),
        (gate.weight (paddingIndex hcore index) *
          bitInt (padding index)).natAbs ≤ bound := by
    intro index
    rw [Int.natAbs_mul]
    have hbit : (bitInt (padding index)).natAbs ≤ 1 := by
      cases padding index <;> simp [bitInt]
    calc
      (gate.weight (paddingIndex hcore index)).natAbs *
          (bitInt (padding index)).natAbs ≤ bound * 1 :=
        Nat.mul_le_mul (hparameters.1 _) hbit
      _ = bound := Nat.mul_one _
  have hfrozen :
      (∑ index : Fin (target - core),
          gate.weight (paddingIndex hcore index) *
            bitInt (padding index)).natAbs ≤ target * bound := by
    calc
      _ ≤ ∑ index : Fin (target - core),
          (gate.weight (paddingIndex hcore index) *
            bitInt (padding index)).natAbs :=
        Int.natAbs_sum_le Finset.univ _
      _ ≤ ∑ _index : Fin (target - core), bound :=
        Finset.sum_le_sum fun index _ => hterm index
      _ = (target - core) * bound := by simp
      _ ≤ target * bound :=
        Nat.mul_le_mul_right bound (Nat.sub_le target core)
  constructor
  · intro index
    change
      (gate.weight (coreIndex hcore index)).natAbs ≤
        restrictedParameterBound target bound
    have hbound := hparameters.1 (coreIndex hcore index)
    unfold restrictedParameterBound
    nlinarith
  · change
      (gate.threshold -
        ∑ index : Fin (target - core),
          gate.weight (paddingIndex hcore index) *
            bitInt (padding index)).natAbs ≤
        restrictedParameterBound target bound
    calc
      _ ≤ gate.threshold.natAbs +
          (∑ index : Fin (target - core),
            gate.weight (paddingIndex hcore index) *
              bitInt (padding index)).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ bound + target * bound :=
        Nat.add_le_add hparameters.2 hfrozen
      _ = restrictedParameterBound target bound := by
        simp [restrictedParameterBound, Nat.add_mul, Nat.add_comm]

/-- Uniform syntax charge for one restricted support-first gate. -/
def restrictedGateDescriptionCap (core target bound : ℕ) : ℕ :=
  (core + 1) * natBitLength (restrictedParameterBound target bound) + core

theorem intBitLength_le_of_natAbs_le_general
    {value : ℤ} {bound : ℕ} (hvalue : value.natAbs ≤ bound) :
    intBitLength value ≤ natBitLength bound := by
  unfold intBitLength natBitLength
  exact Nat.add_le_add_right (Nat.log_mono_right hvalue) 1

theorem encodingBits_le_of_parametersBoundedBy
    {arity bound : ℕ} (gate : NormalizedThresholdGate arity)
    (hparameters : gate.parametersBoundedBy bound) :
    gate.encodingBits ≤ (arity + 1) * natBitLength bound := by
  have hbit :
      ∀ value : ℤ, value.natAbs ≤ bound →
        intBitLength value ≤ natBitLength bound := by
    intro value hvalue
    exact intBitLength_le_of_natAbs_le_general hvalue
  have hthreshold :
      intBitLength gate.threshold ≤ natBitLength bound :=
    hbit gate.threshold hparameters.2
  have hweights :
      (∑ index, intBitLength (gate.weight index)) ≤
        arity * natBitLength bound := by
    simpa using
      (Finset.sum_le_card_nsmul Finset.univ
        (fun index => intBitLength (gate.weight index))
        (natBitLength bound)
        (fun index _ => hbit (gate.weight index) (hparameters.1 index)))
  unfold NormalizedThresholdGate.encodingBits
  calc
    intBitLength gate.threshold +
          ∑ index, intBitLength (gate.weight index) ≤
        natBitLength bound + arity * natBitLength bound :=
      Nat.add_le_add hthreshold hweights
    _ = (arity + 1) * natBitLength bound := by ring

/-- The exact retained support after restriction.  Recomputing it from the
restricted integer weights prevents stale support metadata from entering the
supplier request. -/
def restrictSupportedNormalizedGate {core target : ℕ}
    (gate : SupportedNormalizedGate target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) : SupportedNormalizedGate core where
  gate := restrictNormalizedThresholdGate gate.gate hcore padding
  support := Finset.univ.filter fun index =>
    gate.gate.weight (coreIndex hcore index) ≠ 0
  zeroOutside := by
    intro index hindex
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hindex
    exact not_ne_iff.mp hindex

theorem restrictSupportedNormalizedGate_descriptionBits_le
    {core target bound : ℕ}
    (gate : SupportedNormalizedGate target) (hcore : core ≤ target)
    (padding : BitInput (target - core))
    (hparameters : gate.gate.parametersBoundedBy bound) :
    (restrictSupportedNormalizedGate gate hcore padding).descriptionBits ≤
      restrictedGateDescriptionCap core target bound := by
  exact Nat.add_le_add_right
    (encodingBits_le_of_parametersBoundedBy _
      (restrictNormalizedThresholdGate_parametersBoundedBy
        gate.gate hcore padding hparameters))
    core

theorem restrictSupportedNormalizedGate_eval {core target : ℕ}
    (gate : SupportedNormalizedGate target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) (input : BitInput core) :
    (restrictSupportedNormalizedGate gate hcore padding).eval input =
      gate.eval (fun index =>
        Sum.elim input padding ((finSplitEquiv hcore).symm index)) := by
  exact restrictNormalizedThresholdGate_eval gate.gate hcore padding input

theorem restrictSupportedNormalizedGate_wireCount_le {core target : ℕ}
    (gate : SupportedNormalizedGate target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) :
    (restrictSupportedNormalizedGate gate hcore padding).wireCount ≤
      gate.wireCount := by
  classical
  let restricted := restrictSupportedNormalizedGate gate hcore padding
  let embed : Fin core → Fin target := coreIndex hcore
  have hinjective : Function.Injective embed :=
    (finSplitEquiv hcore).injective.comp Sum.inl_injective
  have hsubset : restricted.support.image embed ⊆ gate.support := by
    intro index hindex
    rcases Finset.mem_image.mp hindex with ⟨source, hsource, rfl⟩
    have hnonzero :
        gate.gate.weight (coreIndex hcore source) ≠ 0 := by
      simpa [restricted, restrictSupportedNormalizedGate] using
        (Finset.mem_filter.mp hsource).2
    by_contra houtside
    exact hnonzero (gate.zeroOutside _ houtside)
  unfold SupportedNormalizedGate.wireCount
  calc
    restricted.support.card =
        (restricted.support.image embed).card := by
      exact (Finset.card_image_of_injective _ hinjective).symm
    _ ≤ gate.support.card := Finset.card_le_card hsubset

def restrictNormalizedSymmetricCircuit {core target : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit target)
    (hcore : core ≤ target) (padding : BitInput (target - core)) :
    NormalizedSymmetricThresholdCircuit core where
  bottomCount := circuit.bottomCount
  bottom index :=
    restrictSupportedNormalizedGate (circuit.bottom index) hcore padding
  top := circuit.top

theorem restrictNormalizedSymmetricCircuit_eval {core target : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit target)
    (hcore : core ≤ target) (padding : BitInput (target - core))
    (input : BitInput core) :
    (restrictNormalizedSymmetricCircuit circuit hcore padding).eval input =
      circuit.eval (fun index =>
        Sum.elim input padding ((finSplitEquiv hcore).symm index)) := by
  unfold NormalizedSymmetricThresholdCircuit.eval
  apply congrArg circuit.top
  apply Fin.ext
  simp only [NormalizedSymmetricThresholdCircuit.acceptedBottomCount,
    restrictNormalizedSymmetricCircuit]
  apply congrArg Finset.card
  ext index
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [restrictSupportedNormalizedGate_eval]

theorem restrictNormalizedSymmetricCircuit_wireCount_le
    {core target : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit target)
    (hcore : core ≤ target) (padding : BitInput (target - core)) :
    (restrictNormalizedSymmetricCircuit circuit hcore padding).wireCount ≤
      circuit.wireCount := by
  unfold NormalizedSymmetricThresholdCircuit.wireCount
  apply Finset.sum_le_sum
  intro index _
  exact Nat.add_le_add_right
    (restrictSupportedNormalizedGate_wireCount_le
      (circuit.bottom index) hcore padding) 1

def restrictNormalizedThresholdCircuit {core target : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit target)
    (hcore : core ≤ target) (padding : BitInput (target - core)) :
    NormalizedThresholdThresholdCircuit core where
  bottomCount := circuit.bottomCount
  bottom index :=
    restrictSupportedNormalizedGate (circuit.bottom index) hcore padding
  top := circuit.top

theorem restrictNormalizedThresholdCircuit_eval {core target : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit target)
    (hcore : core ≤ target) (padding : BitInput (target - core))
    (input : BitInput core) :
    (restrictNormalizedThresholdCircuit circuit hcore padding).eval input =
      circuit.eval (fun index =>
        Sum.elim input padding ((finSplitEquiv hcore).symm index)) := by
  unfold NormalizedThresholdThresholdCircuit.eval
  apply congrArg circuit.top.eval
  funext index
  exact restrictSupportedNormalizedGate_eval
    (circuit.bottom index) hcore padding input

theorem restrictNormalizedThresholdCircuit_wireCount_le
    {core target : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit target)
    (hcore : core ≤ target) (padding : BitInput (target - core)) :
    (restrictNormalizedThresholdCircuit circuit hcore padding).wireCount ≤
      circuit.wireCount := by
  unfold NormalizedThresholdThresholdCircuit.wireCount
  apply Finset.sum_le_sum
  intro index _
  exact Nat.add_le_add_right
    (restrictSupportedNormalizedGate_wireCount_le
      (circuit.bottom index) hcore padding) 1

/-! ## Public description envelopes -/

theorem normalizedGate_parametersBoundedBy_two_pow_encodingBits
    {arity : ℕ} (gate : NormalizedThresholdGate arity) :
    gate.parametersBoundedBy (2 ^ gate.encodingBits) := by
  classical
  have hvalue (value : ℤ) :
      value.natAbs < 2 ^ intBitLength value := by
    simpa [intBitLength] using
      (Nat.lt_pow_succ_log_self Nat.one_lt_two value.natAbs)
  constructor
  · intro index
    have hterm :
        intBitLength (gate.weight index) ≤
          ∑ candidate, intBitLength (gate.weight candidate) := by
      exact Finset.single_le_sum
        (fun candidate _ => Nat.zero_le (intBitLength (gate.weight candidate)))
        (Finset.mem_univ index)
    have hbits :
        intBitLength (gate.weight index) ≤ gate.encodingBits := by
      unfold NormalizedThresholdGate.encodingBits
      omega
    exact (Nat.le_of_lt (hvalue (gate.weight index))).trans
      (Nat.pow_le_pow_right (by omega) hbits)
  · have hbits :
        intBitLength gate.threshold ≤ gate.encodingBits := by
      unfold NormalizedThresholdGate.encodingBits
      omega
    exact (Nat.le_of_lt (hvalue gate.threshold)).trans
      (Nat.pow_le_pow_right (by omega) hbits)

theorem parametersBoundedBy_mono
    {arity left right : ℕ} (gate : NormalizedThresholdGate arity)
    (hparameters : gate.parametersBoundedBy left) (hle : left ≤ right) :
    gate.parametersBoundedBy right :=
  ⟨fun index => (hparameters.1 index).trans hle,
    hparameters.2.trans hle⟩

theorem normalizedSymmetric_bottom_parametersBoundedBy_descriptionBits
    {arity : ℕ} (circuit : NormalizedSymmetricThresholdCircuit arity)
    (index : Fin circuit.bottomCount) :
    (circuit.bottom index).gate.parametersBoundedBy
      (2 ^ circuit.descriptionBits) := by
  classical
  have hterm :
      (circuit.bottom index).descriptionBits ≤
        ∑ candidate, (circuit.bottom candidate).descriptionBits := by
    exact Finset.single_le_sum
      (fun candidate _ =>
        Nat.zero_le (circuit.bottom candidate).descriptionBits)
      (Finset.mem_univ index)
  have hgate :
      (circuit.bottom index).gate.encodingBits ≤
        circuit.descriptionBits := by
    have hgateTerm :
        (circuit.bottom index).gate.encodingBits ≤
          (circuit.bottom index).descriptionBits := by
      unfold SupportedNormalizedGate.descriptionBits
      omega
    have hsumCircuit :
        (∑ candidate, (circuit.bottom candidate).descriptionBits) ≤
          circuit.descriptionBits := by
      unfold NormalizedSymmetricThresholdCircuit.descriptionBits
      omega
    exact hgateTerm.trans (hterm.trans hsumCircuit)
  constructor
  · intro coordinate
    exact
      ((normalizedGate_parametersBoundedBy_two_pow_encodingBits
        (circuit.bottom index).gate).1 coordinate).trans
        (Nat.pow_le_pow_right (by omega) hgate)
  · exact
      (normalizedGate_parametersBoundedBy_two_pow_encodingBits
        (circuit.bottom index).gate).2.trans
        (Nat.pow_le_pow_right (by omega) hgate)

theorem normalizedThreshold_bottom_parametersBoundedBy_descriptionBits
    {arity : ℕ} (circuit : NormalizedThresholdThresholdCircuit arity)
    (index : Fin circuit.bottomCount) :
    (circuit.bottom index).gate.parametersBoundedBy
      (2 ^ circuit.descriptionBits) := by
  classical
  have hterm :
      (circuit.bottom index).descriptionBits ≤
        ∑ candidate, (circuit.bottom candidate).descriptionBits := by
    exact Finset.single_le_sum
      (fun candidate _ =>
        Nat.zero_le (circuit.bottom candidate).descriptionBits)
      (Finset.mem_univ index)
  have hgate :
      (circuit.bottom index).gate.encodingBits ≤
        circuit.descriptionBits := by
    have hgateTerm :
        (circuit.bottom index).gate.encodingBits ≤
          (circuit.bottom index).descriptionBits := by
      unfold SupportedNormalizedGate.descriptionBits
      omega
    have hsumCircuit :
        (∑ candidate, (circuit.bottom candidate).descriptionBits) ≤
          circuit.descriptionBits := by
      unfold NormalizedThresholdThresholdCircuit.descriptionBits
      omega
    exact hgateTerm.trans (hterm.trans hsumCircuit)
  constructor
  · intro coordinate
    exact
      ((normalizedGate_parametersBoundedBy_two_pow_encodingBits
        (circuit.bottom index).gate).1 coordinate).trans
        (Nat.pow_le_pow_right (by omega) hgate)
  · exact
      (normalizedGate_parametersBoundedBy_two_pow_encodingBits
        (circuit.bottom index).gate).2.trans
        (Nat.pow_le_pow_right (by omega) hgate)

def restrictedSymmetricDescriptionCap
    (core target parameterBound wireCap : ℕ) : ℕ :=
  (wireCap + 1) *
    (restrictedGateDescriptionCap core target parameterBound + 1)

def restrictedThresholdDescriptionCap
    (core target parameterBound descriptionCap : ℕ) : ℕ :=
  (descriptionCap + 1) *
    (restrictedGateDescriptionCap core target parameterBound + 1)

theorem restrictNormalizedSymmetricCircuit_descriptionBits_le
    {core target bound wireCap : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit target)
    (hcore : core ≤ target) (padding : BitInput (target - core))
    (hwires : circuit.wireCount ≤ wireCap)
    (hparameters :
      ∀ index, (circuit.bottom index).gate.parametersBoundedBy bound) :
    (restrictNormalizedSymmetricCircuit circuit hcore padding).descriptionBits ≤
      restrictedSymmetricDescriptionCap core target bound wireCap := by
  have hcount : circuit.bottomCount ≤ wireCap := by
    calc
      circuit.bottomCount =
          ∑ _index : Fin circuit.bottomCount, 1 := by simp
      _ ≤ ∑ index : Fin circuit.bottomCount,
          ((circuit.bottom index).wireCount + 1) :=
        Finset.sum_le_sum fun _index _ => Nat.le_add_left 1 _
      _ = circuit.wireCount := rfl
      _ ≤ wireCap := hwires
  have hsum :
      (∑ index,
          ((restrictNormalizedSymmetricCircuit circuit hcore padding).bottom
            index).descriptionBits) ≤
        circuit.bottomCount *
          restrictedGateDescriptionCap core target bound := by
    change
      (∑ index : Fin circuit.bottomCount,
          (restrictSupportedNormalizedGate
            (circuit.bottom index) hcore padding).descriptionBits) ≤
        circuit.bottomCount *
          restrictedGateDescriptionCap core target bound
    calc
      _ ≤ Fintype.card (Fin circuit.bottomCount) *
          restrictedGateDescriptionCap core target bound := by
        simpa [Finset.card_univ] using
          (Finset.sum_le_card_nsmul Finset.univ
            (fun index =>
              (restrictSupportedNormalizedGate
                (circuit.bottom index) hcore padding).descriptionBits)
            (restrictedGateDescriptionCap core target bound)
            (fun index _ =>
              restrictSupportedNormalizedGate_descriptionBits_le
                (circuit.bottom index) hcore padding (hparameters index)))
      _ = circuit.bottomCount *
          restrictedGateDescriptionCap core target bound := by simp
  unfold NormalizedSymmetricThresholdCircuit.descriptionBits
    restrictedSymmetricDescriptionCap
  change
    circuit.bottomCount + 1 +
        (∑ index,
          ((restrictNormalizedSymmetricCircuit circuit hcore padding).bottom
            index).descriptionBits) ≤
      (wireCap + 1) *
        (restrictedGateDescriptionCap core target bound + 1)
  nlinarith

theorem threshold_bottomCount_le_descriptionBits
    {arity : ℕ} (circuit : NormalizedThresholdThresholdCircuit arity) :
    circuit.bottomCount ≤ circuit.descriptionBits := by
  have hone :
      ∀ index : Fin circuit.bottomCount,
        1 ≤ (circuit.bottom index).descriptionBits := by
    intro index
    unfold SupportedNormalizedGate.descriptionBits
      NormalizedThresholdGate.encodingBits intBitLength
    omega
  unfold NormalizedThresholdThresholdCircuit.descriptionBits
  calc
    circuit.bottomCount =
        ∑ _index : Fin circuit.bottomCount, 1 := by simp
    _ ≤ ∑ index : Fin circuit.bottomCount,
        (circuit.bottom index).descriptionBits :=
      Finset.sum_le_sum fun index _ => hone index
    _ ≤ circuit.top.descriptionBits +
        ∑ index : Fin circuit.bottomCount,
          (circuit.bottom index).descriptionBits := by omega

theorem restrictNormalizedThresholdCircuit_descriptionBits_le
    {core target bound descriptionCap : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit target)
    (hcore : core ≤ target) (padding : BitInput (target - core))
    (hdescription : circuit.descriptionBits ≤ descriptionCap)
    (hparameters :
      ∀ index, (circuit.bottom index).gate.parametersBoundedBy bound) :
    (restrictNormalizedThresholdCircuit circuit hcore padding).descriptionBits ≤
      restrictedThresholdDescriptionCap core target bound descriptionCap := by
  have hcount : circuit.bottomCount ≤ descriptionCap :=
    (threshold_bottomCount_le_descriptionBits circuit).trans hdescription
  have htop : circuit.top.descriptionBits ≤ descriptionCap := by
    apply le_trans _ hdescription
    unfold NormalizedThresholdThresholdCircuit.descriptionBits
    omega
  have hsum :
      (∑ index,
          ((restrictNormalizedThresholdCircuit circuit hcore padding).bottom
            index).descriptionBits) ≤
        circuit.bottomCount *
          restrictedGateDescriptionCap core target bound := by
    change
      (∑ index : Fin circuit.bottomCount,
          (restrictSupportedNormalizedGate
            (circuit.bottom index) hcore padding).descriptionBits) ≤
        circuit.bottomCount *
          restrictedGateDescriptionCap core target bound
    calc
      _ ≤ Fintype.card (Fin circuit.bottomCount) *
          restrictedGateDescriptionCap core target bound := by
        simpa [Finset.card_univ] using
          (Finset.sum_le_card_nsmul Finset.univ
            (fun index =>
              (restrictSupportedNormalizedGate
                (circuit.bottom index) hcore padding).descriptionBits)
            (restrictedGateDescriptionCap core target bound)
            (fun index _ =>
              restrictSupportedNormalizedGate_descriptionBits_le
                (circuit.bottom index) hcore padding (hparameters index)))
      _ = circuit.bottomCount *
          restrictedGateDescriptionCap core target bound := by simp
  unfold NormalizedThresholdThresholdCircuit.descriptionBits
    restrictedThresholdDescriptionCap
  change
    circuit.top.descriptionBits +
        (∑ index,
          ((restrictNormalizedThresholdCircuit circuit hcore padding).bottom
            index).descriptionBits) ≤
      (descriptionCap + 1) *
        (restrictedGateDescriptionCap core target bound + 1)
  nlinarith

theorem restrictNormalizedSymmetricCircuit_descriptionBits_le_of_source
    {core target wireCap descriptionCap : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit target)
    (hcore : core ≤ target) (padding : BitInput (target - core))
    (hwires : circuit.wireCount ≤ wireCap)
    (hdescription : circuit.descriptionBits ≤ descriptionCap) :
    (restrictNormalizedSymmetricCircuit circuit hcore padding).descriptionBits ≤
      restrictedSymmetricDescriptionCap core target
        (2 ^ descriptionCap) wireCap := by
  apply restrictNormalizedSymmetricCircuit_descriptionBits_le
    circuit hcore padding hwires
  intro index
  exact parametersBoundedBy_mono _
    (normalizedSymmetric_bottom_parametersBoundedBy_descriptionBits
      circuit index)
    (Nat.pow_le_pow_right (by omega) hdescription)

theorem restrictNormalizedThresholdCircuit_descriptionBits_le_of_source
    {core target descriptionCap : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit target)
    (hcore : core ≤ target) (padding : BitInput (target - core))
    (hdescription : circuit.descriptionBits ≤ descriptionCap) :
    (restrictNormalizedThresholdCircuit circuit hcore padding).descriptionBits ≤
      restrictedThresholdDescriptionCap core target
        (2 ^ descriptionCap) descriptionCap := by
  apply restrictNormalizedThresholdCircuit_descriptionBits_le
    circuit hcore padding hdescription
  intro index
  exact parametersBoundedBy_mono _
    (normalizedThreshold_bottom_parametersBoundedBy_descriptionBits
      circuit index)
    (Nat.pow_le_pow_right (by omega) hdescription)

/-! ## Restriction of complete legal sums -/

/-- Change only the atom carried by a legal term.  Keeping this operation
generic makes coefficient preservation definitionally shared by both circuit
families. -/
def mapLegalCircuitTerm
    {Circuit : CanonicalWitnessCodec.CircuitFamily}
    {sourceArity targetArity : ℕ}
    (mapCircuit : Circuit sourceArity → Circuit targetArity)
    (term : LegalCircuitTerm Circuit sourceArity) :
    LegalCircuitTerm Circuit targetArity where
  coefficient := term.coefficient
  circuit := mapCircuit term.circuit

@[simp] theorem mapLegalCircuitTerm_coefficient
    {Circuit : CanonicalWitnessCodec.CircuitFamily}
    {sourceArity targetArity : ℕ}
    (mapCircuit : Circuit sourceArity → Circuit targetArity)
    (term : LegalCircuitTerm Circuit sourceArity) :
    (mapLegalCircuitTerm mapCircuit term).coefficient = term.coefficient := rfl

theorem mapLegalCircuitTerms_fold
    {Circuit : CanonicalWitnessCodec.CircuitFamily}
    {sourceArity targetArity : ℕ}
    (mapCircuit : Circuit sourceArity → Circuit targetArity)
    (sourceValue : Circuit sourceArity → Bool)
    (targetValue : Circuit targetArity → Bool)
    (hvalue : ∀ circuit, targetValue (mapCircuit circuit) = sourceValue circuit)
    (terms : List (LegalCircuitTerm Circuit sourceArity))
    (initial : ℝ) :
    (terms.map (mapLegalCircuitTerm mapCircuit)).foldl
        (fun total term =>
          total + (term.coefficient : ℝ) * bitAsReal (targetValue term.circuit))
        initial =
      terms.foldl
        (fun total term =>
          total + (term.coefficient : ℝ) * bitAsReal (sourceValue term.circuit))
        initial := by
  induction terms generalizing initial with
  | nil => rfl
  | cons term terms inductionHypothesis =>
      simp only [List.map_cons, List.foldl_cons, mapLegalCircuitTerm]
      rw [hvalue term.circuit]
      exact inductionHypothesis _

theorem mapLegalCircuitTerms_coefficientMass
    {Circuit : CanonicalWitnessCodec.CircuitFamily}
    {sourceArity targetArity : ℕ}
    (mapCircuit : Circuit sourceArity → Circuit targetArity)
    (terms : List (LegalCircuitTerm Circuit sourceArity))
    (initial : ℚ) :
    (terms.map (mapLegalCircuitTerm mapCircuit)).foldl
        (fun total term => total + |term.coefficient|) initial =
      terms.foldl
        (fun total term => total + |term.coefficient|) initial := by
  induction terms generalizing initial with
  | nil => rfl
  | cons term terms inductionHypothesis =>
      simp only [List.map_cons, List.foldl_cons,
        mapLegalCircuitTerm_coefficient]
      exact inductionHypothesis _

def restrictSymmetricLegalCircuitSum {core target : ℕ}
    (value :
      LegalCircuitSumDescription NormalizedSymmetricThresholdCircuit)
    (harity : value.q = target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) :
    LegalCircuitSumDescription NormalizedSymmetricThresholdCircuit where
  q := core
  terms :=
    (cast
      (congrArg
        (fun arity =>
          List (LegalCircuitTerm NormalizedSymmetricThresholdCircuit arity))
        harity)
      value.terms).map fun term =>
        mapLegalCircuitTerm
          (fun circuit =>
            restrictNormalizedSymmetricCircuit circuit hcore padding)
          term

def restrictThresholdLegalCircuitSum {core target : ℕ}
    (value :
      LegalCircuitSumDescription NormalizedThresholdThresholdCircuit)
    (harity : value.q = target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) :
    LegalCircuitSumDescription NormalizedThresholdThresholdCircuit where
  q := core
  terms :=
    (cast
      (congrArg
        (fun arity =>
          List (LegalCircuitTerm NormalizedThresholdThresholdCircuit arity))
        harity)
      value.terms).map fun term =>
        mapLegalCircuitTerm
          (fun circuit =>
            restrictNormalizedThresholdCircuit circuit hcore padding)
          term

theorem restrictSymmetricLegalCircuitSum_length
    {core target : ℕ}
    (value :
      LegalCircuitSumDescription NormalizedSymmetricThresholdCircuit)
    (harity : value.q = target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) :
    (restrictSymmetricLegalCircuitSum value harity hcore padding).terms.length =
      value.terms.length := by
  subst target
  simp [restrictSymmetricLegalCircuitSum]

theorem restrictThresholdLegalCircuitSum_length
    {core target : ℕ}
    (value :
      LegalCircuitSumDescription NormalizedThresholdThresholdCircuit)
    (harity : value.q = target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) :
    (restrictThresholdLegalCircuitSum value harity hcore padding).terms.length =
      value.terms.length := by
  subst target
  simp [restrictThresholdLegalCircuitSum]

theorem restrictSymmetricLegalCircuitSum_coefficients
    {core target : ℕ}
    (value :
      LegalCircuitSumDescription NormalizedSymmetricThresholdCircuit)
    (harity : value.q = target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) :
    (restrictSymmetricLegalCircuitSum value harity hcore padding).terms.map
        (·.coefficient) =
      value.terms.map (·.coefficient) := by
  subst target
  simp [restrictSymmetricLegalCircuitSum]

theorem restrictThresholdLegalCircuitSum_coefficients
    {core target : ℕ}
    (value :
      LegalCircuitSumDescription NormalizedThresholdThresholdCircuit)
    (harity : value.q = target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) :
    (restrictThresholdLegalCircuitSum value harity hcore padding).terms.map
        (·.coefficient) =
      value.terms.map (·.coefficient) := by
  subst target
  simp [restrictThresholdLegalCircuitSum]

theorem restrictSymmetricLegalCircuitSum_coefficientMass
    {core target : ℕ}
    (value :
      LegalCircuitSumDescription NormalizedSymmetricThresholdCircuit)
    (harity : value.q = target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) :
    (restrictSymmetricLegalCircuitSum value harity hcore padding).coefficientMass =
      value.coefficientMass := by
  subst target
  unfold restrictSymmetricLegalCircuitSum
    LegalCircuitSumDescription.coefficientMass
  exact mapLegalCircuitTerms_coefficientMass _ _ 0

theorem restrictThresholdLegalCircuitSum_coefficientMass
    {core target : ℕ}
    (value :
      LegalCircuitSumDescription NormalizedThresholdThresholdCircuit)
    (harity : value.q = target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) :
    (restrictThresholdLegalCircuitSum value harity hcore padding).coefficientMass =
      value.coefficientMass := by
  subst target
  unfold restrictThresholdLegalCircuitSum
    LegalCircuitSumDescription.coefficientMass
  exact mapLegalCircuitTerms_coefficientMass _ _ 0

theorem restrictSymmetricLegalCircuitSum_wires_le
    {core target cap : ℕ}
    (value :
      LegalCircuitSumDescription NormalizedSymmetricThresholdCircuit)
    (harity : value.q = target) (hcore : core ≤ target)
    (padding : BitInput (target - core))
    (hsource : ∀ term ∈ value.terms, term.circuit.wireCount ≤ cap) :
    ∀ term ∈
        (restrictSymmetricLegalCircuitSum value harity hcore padding).terms,
      term.circuit.wireCount ≤ cap := by
  subst target
  intro term hterm
  rcases List.mem_map.mp hterm with ⟨source, hsourceMem, rfl⟩
  exact (restrictNormalizedSymmetricCircuit_wireCount_le
    source.circuit hcore padding).trans (hsource source hsourceMem)

theorem restrictThresholdLegalCircuitSum_wires_le
    {core target cap : ℕ}
    (value :
      LegalCircuitSumDescription NormalizedThresholdThresholdCircuit)
    (harity : value.q = target) (hcore : core ≤ target)
    (padding : BitInput (target - core))
    (hsource : ∀ term ∈ value.terms, term.circuit.wireCount ≤ cap) :
    ∀ term ∈
        (restrictThresholdLegalCircuitSum value harity hcore padding).terms,
      term.circuit.wireCount ≤ cap := by
  subst target
  intro term hterm
  rcases List.mem_map.mp hterm with ⟨source, hsourceMem, rfl⟩
  exact (restrictNormalizedThresholdCircuit_wireCount_le
    source.circuit hcore padding).trans (hsource source hsourceMem)

theorem restrictSymmetricLegalCircuitSum_eval
    {core target : ℕ}
    (value :
      LegalCircuitSumDescription NormalizedSymmetricThresholdCircuit)
    (harity : value.q = target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) (input : BitInput core) :
    (restrictSymmetricLegalCircuitSum value harity hcore padding).terms.foldl
        (fun total term =>
          total + (term.coefficient : ℝ) *
            bitAsReal (term.circuit.eval input)) 0 =
      (cast
        (congrArg
          (fun arity =>
            List (LegalCircuitTerm NormalizedSymmetricThresholdCircuit arity))
          harity)
        value.terms).foldl
        (fun total term =>
          total + (term.coefficient : ℝ) *
            bitAsReal
              (term.circuit.eval (fun index =>
                Sum.elim input padding ((finSplitEquiv hcore).symm index))))
        0 := by
  unfold restrictSymmetricLegalCircuitSum
  exact mapLegalCircuitTerms_fold
    (mapCircuit := fun circuit =>
      restrictNormalizedSymmetricCircuit circuit hcore padding)
    (sourceValue := fun circuit =>
      circuit.eval (fun index =>
        Sum.elim input padding ((finSplitEquiv hcore).symm index)))
    (targetValue := fun circuit => circuit.eval input)
    (fun circuit =>
      restrictNormalizedSymmetricCircuit_eval circuit hcore padding input)
    _ 0

theorem restrictThresholdLegalCircuitSum_eval
    {core target : ℕ}
    (value :
      LegalCircuitSumDescription NormalizedThresholdThresholdCircuit)
    (harity : value.q = target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) (input : BitInput core) :
    (restrictThresholdLegalCircuitSum value harity hcore padding).terms.foldl
        (fun total term =>
          total + (term.coefficient : ℝ) *
            bitAsReal (term.circuit.eval input)) 0 =
      (cast
        (congrArg
          (fun arity =>
            List (LegalCircuitTerm NormalizedThresholdThresholdCircuit arity))
          harity)
        value.terms).foldl
        (fun total term =>
          total + (term.coefficient : ℝ) *
            bitAsReal
              (term.circuit.eval (fun index =>
                Sum.elim input padding ((finSplitEquiv hcore).symm index))))
        0 := by
  unfold restrictThresholdLegalCircuitSum
  exact mapLegalCircuitTerms_fold
    (mapCircuit := fun circuit =>
      restrictNormalizedThresholdCircuit circuit hcore padding)
    (sourceValue := fun circuit =>
      circuit.eval (fun index =>
        Sum.elim input padding ((finSplitEquiv hcore).symm index)))
    (targetValue := fun circuit => circuit.eval input)
    (fun circuit =>
      restrictNormalizedThresholdCircuit_eval circuit hcore padding input)
    _ 0

/-! ## Checked decoder handoff -/

def symmetricRestrictedLimits (source : LegalSumLimits) (core : ℕ) :
    LegalSumLimits where
  expectedArity := core
  termCap := source.termCap
  coefficientBitCap := source.coefficientBitCap
  coefficientMassCap := source.coefficientMassCap
  wireCap := source.wireCap
  descriptionCap :=
    restrictedSymmetricDescriptionCap core source.expectedArity
      (2 ^ source.descriptionCap) source.wireCap

def thresholdRestrictedLimits (source : LegalSumLimits) (core : ℕ) :
    LegalSumLimits where
  expectedArity := core
  termCap := source.termCap
  coefficientBitCap := source.coefficientBitCap
  coefficientMassCap := source.coefficientMassCap
  wireCap := source.wireCap
  descriptionCap :=
    restrictedThresholdDescriptionCap core source.expectedArity
      (2 ^ source.descriptionCap) source.descriptionCap

/-- The typed decoder result is restricted without reopening any of its
canonical syntax checks.  All source caps become fields of the one derived
limits record above. -/
def restrictCheckedSymmetricLegalCircuitSum
    (limits : LegalSumLimits)
    (checked : CheckedLegalCircuitSum
      NormalizedSymmetricThresholdCircuit
      NormalizedSymmetricThresholdCircuit.wireCount
      NormalizedSymmetricThresholdCircuit.descriptionBits limits)
    (core : ℕ) (hcore : core ≤ limits.expectedArity)
    (padding : BitInput (limits.expectedArity - core)) :
    CheckedLegalCircuitSum
      NormalizedSymmetricThresholdCircuit
      NormalizedSymmetricThresholdCircuit.wireCount
      NormalizedSymmetricThresholdCircuit.descriptionBits
      (symmetricRestrictedLimits limits core) := by
  cases checked with
  | mk value harity hterms hbits hmass hwires hdescription =>
      cases value with
      | mk q terms =>
          dsimp only at harity
          subst q
          let source :
              LegalCircuitSumDescription
                NormalizedSymmetricThresholdCircuit :=
            ⟨limits.expectedArity, terms⟩
          let restricted :=
            restrictSymmetricLegalCircuitSum source rfl hcore padding
          refine
            { value := restricted
              arity_eq := rfl
              terms_le := ?_
              coefficient_bits_le := ?_
              mass_le := ?_
              wires_le := ?_
              description_le := ?_ }
          · rw [restrictSymmetricLegalCircuitSum_length]
            exact hterms
          · intro term hterm
            rcases List.mem_map.mp hterm with
              ⟨sourceTerm, hsourceTerm, rfl⟩
            exact hbits sourceTerm hsourceTerm
          · rw [restrictSymmetricLegalCircuitSum_coefficientMass]
            exact hmass
          · exact restrictSymmetricLegalCircuitSum_wires_le
              source rfl hcore padding hwires
          · intro term hterm
            rcases List.mem_map.mp hterm with
              ⟨sourceTerm, hsourceTerm, rfl⟩
            exact
              restrictNormalizedSymmetricCircuit_descriptionBits_le_of_source
                sourceTerm.circuit hcore padding
                (hwires sourceTerm hsourceTerm)
                (hdescription sourceTerm hsourceTerm)

def restrictCheckedThresholdLegalCircuitSum
    (limits : LegalSumLimits)
    (checked : CheckedLegalCircuitSum
      NormalizedThresholdThresholdCircuit
      NormalizedThresholdThresholdCircuit.wireCount
      NormalizedThresholdThresholdCircuit.descriptionBits limits)
    (core : ℕ) (hcore : core ≤ limits.expectedArity)
    (padding : BitInput (limits.expectedArity - core)) :
    CheckedLegalCircuitSum
      NormalizedThresholdThresholdCircuit
      NormalizedThresholdThresholdCircuit.wireCount
      NormalizedThresholdThresholdCircuit.descriptionBits
      (thresholdRestrictedLimits limits core) := by
  cases checked with
  | mk value harity hterms hbits hmass hwires hdescription =>
      cases value with
      | mk q terms =>
          dsimp only at harity
          subst q
          let source :
              LegalCircuitSumDescription
                NormalizedThresholdThresholdCircuit :=
            ⟨limits.expectedArity, terms⟩
          let restricted :=
            restrictThresholdLegalCircuitSum source rfl hcore padding
          refine
            { value := restricted
              arity_eq := rfl
              terms_le := ?_
              coefficient_bits_le := ?_
              mass_le := ?_
              wires_le := ?_
              description_le := ?_ }
          · rw [restrictThresholdLegalCircuitSum_length]
            exact hterms
          · intro term hterm
            rcases List.mem_map.mp hterm with
              ⟨sourceTerm, hsourceTerm, rfl⟩
            exact hbits sourceTerm hsourceTerm
          · rw [restrictThresholdLegalCircuitSum_coefficientMass]
            exact hmass
          · exact restrictThresholdLegalCircuitSum_wires_le
              source rfl hcore padding hwires
          · intro term hterm
            rcases List.mem_map.mp hterm with
              ⟨sourceTerm, hsourceTerm, rfl⟩
            exact
              restrictNormalizedThresholdCircuit_descriptionBits_le_of_source
                sourceTerm.circuit hcore padding
                (hdescription sourceTerm hsourceTerm)

end NearCubicWires.ComponentwiseCircuitRestriction
