import Proof.Foundations.SupplierPipeline

/-!
# Zero-advice pairwise-hash concentration

This module proves the algebraic and probabilistic core of the pointwise list
construction.  A single affine-hash seed is fixed independently of the input:
distinct labels give exactly uniform, independent field values.  Centered
per-label contributions therefore have no cross terms, yielding the finite
second-moment and Chebyshev bounds used by the nested list.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.SupplierList

open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

noncomputable def realMean {Sample : Type} [Fintype Sample]
    (value : Sample → ℝ) : ℝ :=
  (∑ sample, value sample) / Fintype.card Sample

def affineHash {𝔽 : Type} [Field 𝔽]
    (label : 𝔽) (seed : 𝔽 × 𝔽) : 𝔽 :=
  seed.1 * label + seed.2

/-- Keeping the multiplier as the first coordinate exposes uniformity of one
affine-hash output without any cardinality arithmetic. -/
def affineHashEquiv {𝔽 : Type} [Field 𝔽] (label : 𝔽) :
    𝔽 × 𝔽 ≃ 𝔽 × 𝔽 where
  toFun seed := (seed.1, affineHash label seed)
  invFun output := (output.1, output.2 - output.1 * label)
  left_inv seed := by
    ext <;> simp [affineHash]
  right_inv output := by
    ext <;> simp [affineHash]

/-- Two affine evaluations at distinct labels are an invertible linear change
of the two seed coordinates.  This is the exact pairwise-independence fact;
there is no probabilistic oracle or input-dependent choice. -/
noncomputable def affineHashPairEquiv
    {𝔽 : Type} [Field 𝔽] (leftLabel rightLabel : 𝔽)
    (hdistinct : leftLabel ≠ rightLabel) :
    𝔽 × 𝔽 ≃ 𝔽 × 𝔽 where
  toFun seed :=
    (affineHash leftLabel seed, affineHash rightLabel seed)
  invFun output :=
    let multiplier :=
      (output.1 - output.2) / (leftLabel - rightLabel)
    (multiplier, output.1 - multiplier * leftLabel)
  left_inv seed := by
    have hdifference : leftLabel - rightLabel ≠ 0 := sub_ne_zero.mpr hdistinct
    dsimp [affineHash]
    ext <;> field_simp <;> ring
  right_inv output := by
    have hdifference : leftLabel - rightLabel ≠ 0 := sub_ne_zero.mpr hdistinct
    dsimp [affineHash]
    ext <;> field_simp <;> ring

theorem sum_affineHash
    {𝔽 : Type} [Field 𝔽] [Fintype 𝔽]
    (label : 𝔽) (value : 𝔽 → ℝ) :
    ∑ seed : 𝔽 × 𝔽, value (affineHash label seed) =
      Fintype.card 𝔽 * ∑ output : 𝔽, value output := by
  calc
    (∑ seed : 𝔽 × 𝔽, value (affineHash label seed)) =
        ∑ output : 𝔽 × 𝔽, value output.2 :=
      (affineHashEquiv label).sum_comp (fun output => value output.2)
    _ = Fintype.card 𝔽 * ∑ output : 𝔽, value output := by
      rw [Fintype.sum_prod_type]
      simp

theorem sum_affineHash_pair
    {𝔽 : Type} [Field 𝔽] [Fintype 𝔽]
    (leftLabel rightLabel : 𝔽)
    (hdistinct : leftLabel ≠ rightLabel)
    (value : 𝔽 → 𝔽 → ℝ) :
    ∑ seed : 𝔽 × 𝔽,
        value (affineHash leftLabel seed) (affineHash rightLabel seed) =
      ∑ leftOutput : 𝔽, ∑ rightOutput : 𝔽,
        value leftOutput rightOutput := by
  calc
    (∑ seed : 𝔽 × 𝔽,
        value (affineHash leftLabel seed) (affineHash rightLabel seed)) =
        ∑ output : 𝔽 × 𝔽, value output.1 output.2 :=
      (affineHashPairEquiv leftLabel rightLabel hdistinct).sum_comp
        (fun output => value output.1 output.2)
    _ = ∑ leftOutput : 𝔽, ∑ rightOutput : 𝔽,
        value leftOutput rightOutput := by
      rw [Fintype.sum_prod_type]

theorem sum_affineHash_product_eq_zero
    {𝔽 : Type} [Field 𝔽] [Fintype 𝔽]
    (leftLabel rightLabel : 𝔽)
    (hdistinct : leftLabel ≠ rightLabel)
    (leftValue rightValue : 𝔽 → ℝ)
    (hleftCentered : ∑ output, leftValue output = 0)
    (hrightCentered : ∑ output, rightValue output = 0) :
    ∑ seed : 𝔽 × 𝔽,
        leftValue (affineHash leftLabel seed) *
          rightValue (affineHash rightLabel seed) = 0 := by
  rw [sum_affineHash_pair leftLabel rightLabel hdistinct
    (fun leftOutput rightOutput =>
      leftValue leftOutput * rightValue rightOutput)]
  calc
    (∑ leftOutput : 𝔽, ∑ rightOutput : 𝔽,
        leftValue leftOutput * rightValue rightOutput) =
        (∑ leftOutput : 𝔽, leftValue leftOutput) *
          ∑ rightOutput : 𝔽, rightValue rightOutput := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = 0 := by rw [hleftCentered, hrightCentered]; ring

def affineAggregate
    {Index 𝔽 : Type} [Field 𝔽] [DecidableEq Index]
    (active : Finset Index) (label : Index → 𝔽)
    (contribution : Index → 𝔽 → ℝ) (seed : 𝔽 × 𝔽) : ℝ :=
  ∑ index ∈ active, contribution index (affineHash (label index) seed)

theorem sum_affineAggregate
    {Index 𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq Index]
    (active : Finset Index) (label : Index → 𝔽)
    (contribution : Index → 𝔽 → ℝ)
    (hcentered : ∀ index ∈ active,
      ∑ output, contribution index output = 0) :
    ∑ seed : 𝔽 × 𝔽,
        affineAggregate active label contribution seed = 0 := by
  unfold affineAggregate
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro index hindex
  rw [sum_affineHash, hcentered index hindex]
  ring

/-- Pairwise independence removes every off-diagonal term in the square of
the active-coordinate sum.  This equality is the finite, exact form of the
variance calculation in the zero-advice list proof. -/
theorem sum_affineAggregate_sq
    {Index 𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq Index]
    (active : Finset Index) (label : Index → 𝔽)
    (contribution : Index → 𝔽 → ℝ)
    (hlabels : ∀ left ∈ active, ∀ right ∈ active,
      left ≠ right → label left ≠ label right)
    (hcentered : ∀ index ∈ active,
      ∑ output, contribution index output = 0) :
    ∑ seed : 𝔽 × 𝔽,
        affineAggregate active label contribution seed ^ 2 =
      Fintype.card 𝔽 *
        ∑ index ∈ active, ∑ output : 𝔽, contribution index output ^ 2 := by
  unfold affineAggregate
  calc
    (∑ seed : 𝔽 × 𝔽,
        (∑ index ∈ active,
          contribution index (affineHash (label index) seed)) ^ 2) =
        ∑ left ∈ active, ∑ right ∈ active, ∑ seed : 𝔽 × 𝔽,
          contribution left (affineHash (label left) seed) *
            contribution right (affineHash (label right) seed) := by
      simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro left _
      rw [Finset.sum_comm]
    _ = ∑ index ∈ active, ∑ seed : 𝔽 × 𝔽,
          contribution index (affineHash (label index) seed) *
            contribution index (affineHash (label index) seed) := by
      apply Finset.sum_congr rfl
      intro left hleft
      apply Finset.sum_eq_single left
      · intro right hright hrightNe
        exact sum_affineHash_product_eq_zero
          (label left) (label right)
          (hlabels left hleft right hright hrightNe.symm)
          (contribution left) (contribution right)
          (hcentered left hleft) (hcentered right hright)
      · intro hleftMissing
        exact (hleftMissing hleft).elim
    _ = ∑ index ∈ active,
          Fintype.card 𝔽 *
            ∑ output : 𝔽,
              contribution index output * contribution index output := by
      apply Finset.sum_congr rfl
      intro index _
      exact sum_affineHash (label index)
        (fun output =>
          contribution index output * contribution index output)
    _ = Fintype.card 𝔽 *
        ∑ index ∈ active, ∑ output : 𝔽,
          contribution index output ^ 2 := by
      rw [Finset.mul_sum]
      simp [pow_two]

theorem realMean_affineAggregate_sq
    {Index 𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq Index]
    (active : Finset Index) (label : Index → 𝔽)
    (contribution : Index → 𝔽 → ℝ)
    (hlabels : ∀ left ∈ active, ∀ right ∈ active,
      left ≠ right → label left ≠ label right)
    (hcentered : ∀ index ∈ active,
      ∑ output, contribution index output = 0) :
    realMean (fun seed : 𝔽 × 𝔽 =>
      affineAggregate active label contribution seed ^ 2) =
      ∑ index ∈ active,
        realMean (fun output : 𝔽 => contribution index output ^ 2) := by
  have hcard : (Fintype.card 𝔽 : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold realMean
  rw [sum_affineAggregate_sq active label contribution hlabels hcentered]
  simp only [Fintype.card_prod, Nat.cast_mul]
  calc
    (Fintype.card 𝔽 : ℝ) *
          (∑ index ∈ active,
            ∑ output : 𝔽, contribution index output ^ 2) /
        ((Fintype.card 𝔽 : ℝ) * Fintype.card 𝔽) =
        (∑ index ∈ active,
          ∑ output : 𝔽, contribution index output ^ 2) /
            Fintype.card 𝔽 :=
      mul_div_mul_left _ _ hcard
    _ = ∑ index ∈ active,
        (∑ output : 𝔽, contribution index output ^ 2) /
          Fintype.card 𝔽 := Finset.sum_div _ _ _

theorem realMean_affineAggregate_sq_le
    {Index 𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq Index]
    (active : Finset Index) (label : Index → 𝔽)
    (contribution : Index → 𝔽 → ℝ)
    (variance : ℝ)
    (hlabels : ∀ left ∈ active, ∀ right ∈ active,
      left ≠ right → label left ≠ label right)
    (hcentered : ∀ index ∈ active,
      ∑ output, contribution index output = 0)
    (hvariance : ∀ index ∈ active,
      realMean (fun output : 𝔽 => contribution index output ^ 2) ≤
        variance) :
    realMean (fun seed : 𝔽 × 𝔽 =>
      affineAggregate active label contribution seed ^ 2) ≤
      active.card * variance := by
  rw [realMean_affineAggregate_sq active label contribution
    hlabels hcentered]
  calc
    (∑ index ∈ active,
        realMean (fun output : 𝔽 =>
          contribution index output ^ 2)) ≤
        ∑ _index ∈ active, variance :=
      Finset.sum_le_sum fun index hindex => hvariance index hindex
    _ = active.card * variance := by simp

theorem bitAsReal_abs_gt_le_square
    (value threshold : ℝ) (hthreshold : 0 < threshold) :
    bitAsReal (decide (threshold < |value|)) ≤
      value ^ 2 / threshold ^ 2 := by
  by_cases hlarge : threshold < |value|
  · have hdecision : decide (threshold < |value|) = true := by
      simp [hlarge]
    simp only [hdecision, bitAsReal, if_true]
    rw [one_le_div (by positivity : 0 < threshold ^ 2)]
    calc
      threshold ^ 2 ≤ |value| ^ 2 :=
        (sq_le_sq₀ hthreshold.le (abs_nonneg value)).2 hlarge.le
      _ = value ^ 2 := sq_abs value
  · have hdecision : decide (threshold < |value|) = false := by
      simp [hlarge]
    simp only [hdecision, bitAsReal]
    positivity

/-- Finite Chebyshev inequality in exactly the `booleanMean` convention used
by the supplier contracts. -/
theorem booleanMean_abs_gt_le
    {Sample : Type} [Fintype Sample] [Nonempty Sample]
    (value : Sample → ℝ) (threshold variance : ℝ)
    (hthreshold : 0 < threshold)
    (hsecond :
      realMean (fun sample => value sample ^ 2) ≤ variance) :
    booleanMean (fun sample => decide (threshold < |value sample|)) ≤
      variance / threshold ^ 2 := by
  have hcard : (0 : ℝ) < Fintype.card Sample := by
    exact_mod_cast Fintype.card_pos
  have hsecondRaw :
      (∑ sample, value sample ^ 2) / Fintype.card Sample ≤ variance := by
    simpa [realMean] using hsecond
  unfold booleanMean
  calc
    (∑ sample, bitAsReal (decide (threshold < |value sample|))) /
          Fintype.card Sample ≤
        (∑ sample, value sample ^ 2 / threshold ^ 2) /
          Fintype.card Sample := by
      apply div_le_div_of_nonneg_right _ hcard.le
      exact Finset.sum_le_sum fun sample _ =>
        bitAsReal_abs_gt_le_square (value sample) threshold hthreshold
    _ = ((∑ sample, value sample ^ 2) / Fintype.card Sample) /
          threshold ^ 2 := by
      rw [← Finset.sum_div]
      ring
    _ ≤ variance / threshold ^ 2 := by
      exact div_le_div_of_nonneg_right hsecondRaw (sq_nonneg threshold)

theorem affineAggregate_chebyshev
    {Index 𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq Index]
    (active : Finset Index) (label : Index → 𝔽)
    (contribution : Index → 𝔽 → ℝ)
    (coordinateVariance threshold : ℝ)
    (hlabels : ∀ left ∈ active, ∀ right ∈ active,
      left ≠ right → label left ≠ label right)
    (hcentered : ∀ index ∈ active,
      ∑ output, contribution index output = 0)
    (hvariance : ∀ index ∈ active,
      realMean (fun output : 𝔽 => contribution index output ^ 2) ≤
        coordinateVariance)
    (hthreshold : 0 < threshold) :
    booleanMean (fun seed : 𝔽 × 𝔽 =>
      decide (threshold <
        |affineAggregate active label contribution seed|)) ≤
      (active.card * coordinateVariance) / threshold ^ 2 := by
  letI : Nonempty (𝔽 × 𝔽) := ⟨(0, 0)⟩
  exact booleanMean_abs_gt_le
    (fun seed => affineAggregate active label contribution seed)
    threshold (active.card * coordinateVariance) hthreshold
    (realMean_affineAggregate_sq_le active label contribution
      coordinateVariance hlabels hcentered hvariance)

def signedSlice {𝔽 : Type} [DecidableEq 𝔽]
    (positive negative : Finset 𝔽) (output : 𝔽) : ℝ :=
  if output ∈ positive then 1
  else if output ∈ negative then -1
  else 0

theorem sum_signedSlice
    {𝔽 : Type} [Fintype 𝔽] [DecidableEq 𝔽]
    (positive negative : Finset 𝔽)
    (hdisjoint : Disjoint positive negative) :
    ∑ output, signedSlice positive negative output =
      positive.card - negative.card := by
  have hpointwise : ∀ output : 𝔽,
      signedSlice positive negative output =
        (if output ∈ positive then 1 else 0) -
          if output ∈ negative then 1 else 0 := by
    intro output
    by_cases hpositive : output ∈ positive
    · have hnegative : output ∉ negative :=
        Finset.disjoint_left.mp hdisjoint hpositive
      simp [signedSlice, hpositive, hnegative]
    · by_cases hnegative : output ∈ negative
      · simp [signedSlice, hpositive, hnegative]
      · simp [signedSlice, hpositive, hnegative]
  simp_rw [hpointwise, Finset.sum_sub_distrib]
  simp

theorem sum_signedSlice_sq
    {𝔽 : Type} [Fintype 𝔽] [DecidableEq 𝔽]
    (positive negative : Finset 𝔽)
    (hdisjoint : Disjoint positive negative) :
    ∑ output, signedSlice positive negative output ^ 2 =
      positive.card + negative.card := by
  have hpointwise : ∀ output : 𝔽,
      signedSlice positive negative output ^ 2 =
        (if output ∈ positive then 1 else 0) +
          if output ∈ negative then 1 else 0 := by
    intro output
    by_cases hpositive : output ∈ positive
    · have hnegative : output ∉ negative :=
        Finset.disjoint_left.mp hdisjoint hpositive
      simp [signedSlice, hpositive, hnegative]
    · by_cases hnegative : output ∈ negative
      · simp [signedSlice, hpositive, hnegative]
      · simp [signedSlice, hpositive, hnegative]
  simp_rw [hpointwise, Finset.sum_add_distrib]
  simp

theorem realMean_signedSlice_sq
    {𝔽 : Type} [Fintype 𝔽] [DecidableEq 𝔽]
    (positive negative : Finset 𝔽)
    (hdisjoint : Disjoint positive negative) :
    realMean (fun output : 𝔽 =>
      signedSlice positive negative output ^ 2) =
      (positive.card + negative.card) / Fintype.card 𝔽 := by
  simp [realMean, sum_signedSlice_sq positive negative hdisjoint]

/-- The manuscript's level-`j` estimate, isolated from the later union and
reconstruction steps.  `positive` and `negative` are the two balanced prefix
cells contributing `+1` and `-1`; their combined density is at most `2⁻ʲ`. -/
theorem affineSignedSlice_chebyshev
    {Index 𝔽 : Type} [Field 𝔽] [Fintype 𝔽]
    [DecidableEq Index] [DecidableEq 𝔽]
    (active : Finset Index) (label : Index → 𝔽)
    (positive negative : Finset 𝔽)
    (level activeBound : ℕ) (threshold : ℝ)
    (hlabels : ∀ left ∈ active, ∀ right ∈ active,
      left ≠ right → label left ≠ label right)
    (hdisjoint : Disjoint positive negative)
    (hbalanced : positive.card = negative.card)
    (hactive : active.card ≤ activeBound)
    (hdensity :
      ((positive.card + negative.card : ℕ) : ℝ) / Fintype.card 𝔽 ≤
        1 / (2 : ℝ) ^ level)
    (hthreshold : 0 < threshold) :
    booleanMean (fun seed : 𝔽 × 𝔽 =>
      decide (threshold <
        |affineAggregate active label
          (fun _index => signedSlice positive negative) seed|)) ≤
      ((activeBound : ℝ) * (1 / (2 : ℝ) ^ level)) /
        threshold ^ 2 := by
  have hcentered : ∀ index ∈ active,
      ∑ output : 𝔽, signedSlice positive negative output = 0 := by
    intro _index _
    rw [sum_signedSlice positive negative hdisjoint, hbalanced]
    simp
  have hvariance : ∀ index ∈ active,
      realMean (fun output : 𝔽 =>
        signedSlice positive negative output ^ 2) ≤
          1 / (2 : ℝ) ^ level := by
    intro _index _
    rw [realMean_signedSlice_sq positive negative hdisjoint]
    simpa only [Nat.cast_add] using hdensity
  have hbase := affineAggregate_chebyshev active label
    (fun _index => signedSlice positive negative)
    (1 / (2 : ℝ) ^ level) threshold hlabels hcentered hvariance hthreshold
  calc
    booleanMean (fun seed : 𝔽 × 𝔽 =>
        decide (threshold <
          |affineAggregate active label
            (fun _index => signedSlice positive negative) seed|)) ≤
        ((active.card : ℝ) * (1 / (2 : ℝ) ^ level)) /
          threshold ^ 2 := hbase
    _ ≤ ((activeBound : ℝ) * (1 / (2 : ℝ) ^ level)) /
          threshold ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg threshold)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hactive

/-! ## Exact downward reconstruction -/

def boundedOneHot (bound total : ℕ) : Fin (bound + 1) → Bool :=
  fun candidate => decide (candidate.val = total)

def reconstructOneHotLayer (bound : ℕ) (delta : ℤ)
    (next : Fin (bound + 1) → Bool) :
    Fin (bound + 1) → Bool :=
  fun candidate =>
    decide (∃ nextCandidate : Fin (bound + 1),
      next nextCandidate = true ∧
        (candidate.val : ℤ) =
          2 * (nextCandidate.val : ℤ) + delta)

theorem reconstructOneHotLayer_correct
    (bound parent child : ℕ) (delta : ℤ)
    (_hparent : parent ≤ bound) (hchild : child ≤ bound)
    (hrelation : (parent : ℤ) = 2 * (child : ℤ) + delta) :
    reconstructOneHotLayer bound delta (boundedOneHot bound child) =
      boundedOneHot bound parent := by
  funext candidate
  apply Bool.eq_iff_iff.mpr
  simp only [reconstructOneHotLayer, boundedOneHot,
    decide_eq_true_eq]
  constructor
  · rintro ⟨nextCandidate, hnext, heq⟩
    have hnextValue : nextCandidate.val = child := by
      exact hnext
    rw [hnextValue] at heq
    exact_mod_cast heq.trans hrelation.symm
  · intro hcandidate
    have hcandidateValue : candidate.val = parent :=
      hcandidate
    let nextCandidate : Fin (bound + 1) :=
      ⟨child, by omega⟩
    refine ⟨nextCandidate, ?_, ?_⟩
    · simp [nextCandidate]
    · simpa [nextCandidate, hcandidateValue] using hrelation

def reconstructOneHot (bound : ℕ) :
    List ℤ → (Fin (bound + 1) → Bool) → Fin (bound + 1) → Bool
  | [], terminal => terminal
  | delta :: rest, terminal =>
      reconstructOneHotLayer bound delta
        (reconstructOneHot bound rest terminal)

/-- A top-to-bottom list of exact count differences.  The tail reconstructs
the child count first; the head then applies `parent = 2*child + delta`. -/
inductive ExactCountRecurrence (bound terminal : ℕ) :
    ℕ → List ℤ → Prop
  | terminal (hterminal : terminal ≤ bound) :
      ExactCountRecurrence bound terminal terminal []
  | step {parent child : ℕ} {delta : ℤ} {rest : List ℤ}
      (hparent : parent ≤ bound)
      (hrelation : (parent : ℤ) = 2 * (child : ℤ) + delta)
      (tail : ExactCountRecurrence bound terminal child rest) :
      ExactCountRecurrence bound terminal parent (delta :: rest)

theorem reconstructOneHot_correct
    {bound terminal parent : ℕ} {deltas : List ℤ}
    (recurrence : ExactCountRecurrence bound terminal parent deltas) :
    reconstructOneHot bound deltas (boundedOneHot bound terminal) =
      boundedOneHot bound parent := by
  induction recurrence with
  | terminal hterminal => rfl
  | @step parent child delta rest hparent hrelation tail ih =>
      simp only [reconstructOneHot]
      rw [ih]
      exact reconstructOneHotLayer_correct bound parent child delta
        hparent
        (by
          cases tail with
          | terminal hterminal => exact hterminal
          | step hchild _ _ => exact hchild)
        hrelation

/-! ## Finite union and terminal-count bounds -/

theorem bitAsReal_nonnegative (value : Bool) :
    0 ≤ bitAsReal value := by
  cases value <;> simp [bitAsReal]

theorem booleanMean_exists_le_sum
    {Sample Level : Type} [Fintype Sample] [Nonempty Sample] [Fintype Level]
    (event : Level → Sample → Bool) :
    booleanMean (fun sample => decide (∃ level, event level sample = true)) ≤
      ∑ level, booleanMean (event level) := by
  have hpointwise : ∀ sample,
      bitAsReal (decide (∃ level, event level sample = true)) ≤
        ∑ level, bitAsReal (event level sample) := by
    intro sample
    by_cases hexists : ∃ level, event level sample = true
    · obtain ⟨level, hlevel⟩ := hexists
      have hsingle :
          bitAsReal (event level sample) ≤
            ∑ candidate, bitAsReal (event candidate sample) := by
        exact Finset.single_le_sum
          (fun candidate _ => bitAsReal_nonnegative (event candidate sample))
          (Finset.mem_univ level)
      have hleft :
          bitAsReal (decide (∃ level, event level sample = true)) = 1 := by
        have hexistsAgain : ∃ candidate, event candidate sample = true :=
          ⟨level, hlevel⟩
        simp [hexistsAgain, bitAsReal]
      have hselected : bitAsReal (event level sample) = 1 := by
        simp [hlevel, bitAsReal]
      rw [hleft, ← hselected]
      exact hsingle
    · have hleft :
          bitAsReal (decide (∃ level, event level sample = true)) = 0 := by
        simp [hexists, bitAsReal]
      rw [hleft]
      exact Finset.sum_nonneg fun level _ =>
        bitAsReal_nonnegative (event level sample)
  unfold booleanMean
  calc
    (∑ sample,
        bitAsReal (decide (∃ level, event level sample = true))) /
          Fintype.card Sample ≤
        (∑ sample, ∑ level, bitAsReal (event level sample)) /
          Fintype.card Sample := by
      apply div_le_div_of_nonneg_right
        (Finset.sum_le_sum fun sample _ => hpointwise sample)
      positivity
    _ = ∑ level,
        (∑ sample, bitAsReal (event level sample)) /
          Fintype.card Sample := by
      rw [Finset.sum_comm, Finset.sum_div]

theorem bitAsReal_positiveNat_le (value : ℕ) :
    bitAsReal (decide (0 < value)) ≤ value := by
  by_cases hpositive : 0 < value
  · have hone : 1 ≤ value := hpositive
    simpa [hpositive, bitAsReal] using hone
  · simp [hpositive, bitAsReal]

theorem booleanMean_positiveNat_le_realMean
    {Sample : Type} [Fintype Sample] [Nonempty Sample]
    (value : Sample → ℕ) :
    booleanMean (fun sample => decide (0 < value sample)) ≤
      realMean (fun sample => value sample) := by
  unfold booleanMean realMean
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum fun sample _ =>
      bitAsReal_positiveNat_le (value sample)
  · positivity

/-- A failure covered by the terminal overflow or one bad level pays exactly
the terminal first moment plus the sum of level errors. -/
theorem nestedFailure_unionBound
    {Sample Level : Type} [Fintype Sample] [Nonempty Sample] [Fintype Level]
    (failure terminalBad : Sample → Bool)
    (levelBad : Level → Sample → Bool)
    (hcovered : ∀ sample, failure sample = true →
      terminalBad sample = true ∨
        ∃ level, levelBad level sample = true) :
    booleanMean failure ≤
      booleanMean terminalBad + ∑ level, booleanMean (levelBad level) := by
  have hpointwise : ∀ sample,
      bitAsReal (failure sample) ≤
        bitAsReal (terminalBad sample) +
          bitAsReal (decide (∃ level, levelBad level sample = true)) := by
    intro sample
    by_cases hfailure : failure sample = true
    · rcases hcovered sample hfailure with hterminal | hlevel
      · have hfailureReal : bitAsReal (failure sample) = 1 := by
          simp [hfailure, bitAsReal]
        have hterminalReal : bitAsReal (terminalBad sample) = 1 := by
          simp [hterminal, bitAsReal]
        rw [hfailureReal, hterminalReal]
        exact le_add_of_nonneg_right
          (bitAsReal_nonnegative
            (decide (∃ level, levelBad level sample = true)))
      · have hexists : ∃ level, levelBad level sample = true := hlevel
        have hfailureReal : bitAsReal (failure sample) = 1 := by
          simp [hfailure, bitAsReal]
        have hexistsReal :
            bitAsReal
              (decide (∃ level, levelBad level sample = true)) = 1 := by
          simp [hexists, bitAsReal]
        rw [hfailureReal, hexistsReal]
        exact le_add_of_nonneg_left
          (bitAsReal_nonnegative (terminalBad sample))
    · have hfailureFalse : failure sample = false := Bool.eq_false_of_not_eq_true hfailure
      have hfailureReal : bitAsReal (failure sample) = 0 := by
        simp [hfailureFalse, bitAsReal]
      rw [hfailureReal]
      exact add_nonneg
        (bitAsReal_nonnegative (terminalBad sample))
        (bitAsReal_nonnegative
          (decide (∃ level, levelBad level sample = true)))
  have hcard : (0 : ℝ) ≤ Fintype.card Sample := by positivity
  calc
    booleanMean failure ≤
        booleanMean terminalBad +
          booleanMean
            (fun sample =>
              decide (∃ level, levelBad level sample = true)) := by
      unfold booleanMean
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hcard
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun sample _ => hpointwise sample
    _ ≤ booleanMean terminalBad +
        ∑ level, booleanMean (levelBad level) := by
      gcongr
      exact booleanMean_exists_le_sum levelBad

def affineCellCount
    {Index 𝔽 : Type} [Field 𝔽] [DecidableEq Index] [DecidableEq 𝔽]
    (active : Finset Index) (label : Index → 𝔽) (cell : Finset 𝔽)
    (seed : 𝔽 × 𝔽) : ℕ :=
  ∑ index ∈ active,
    (decide (affineHash (label index) seed ∈ cell) : Bool).toNat

theorem bitAsReal_eq_toNat (value : Bool) :
    bitAsReal value = value.toNat := by
  cases value <;> simp [bitAsReal]

theorem realMean_affineCellCount
    {Index 𝔽 : Type} [Field 𝔽] [Fintype 𝔽]
    [DecidableEq Index] [DecidableEq 𝔽]
    (active : Finset Index) (label : Index → 𝔽) (cell : Finset 𝔽) :
    realMean (fun seed : 𝔽 × 𝔽 =>
      (affineCellCount active label cell seed : ℝ)) =
      active.card * (cell.card / Fintype.card 𝔽 : ℝ) := by
  have hcard : (Fintype.card 𝔽 : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold realMean affineCellCount
  push_cast
  simp_rw [← bitAsReal_eq_toNat]
  rw [Finset.sum_comm]
  have hperIndex : ∀ index ∈ active,
      ∑ seed : 𝔽 × 𝔽,
          bitAsReal
            (decide (affineHash (label index) seed ∈ cell)) =
        Fintype.card 𝔽 * cell.card := by
    intro index _
    calc
      (∑ seed : 𝔽 × 𝔽,
          bitAsReal
            (decide (affineHash (label index) seed ∈ cell))) =
          Fintype.card 𝔽 *
            ∑ output : 𝔽,
              bitAsReal (decide (output ∈ cell)) :=
        sum_affineHash (label index)
          (fun output => bitAsReal (decide (output ∈ cell)))
      _ = Fintype.card 𝔽 * cell.card := by
        congr 1
        simp [bitAsReal]
  have hsum :
      (∑ index ∈ active, ∑ seed : 𝔽 × 𝔽,
          bitAsReal
            (decide (affineHash (label index) seed ∈ cell))) =
        ∑ _index ∈ active,
          (Fintype.card 𝔽 : ℝ) * cell.card := by
    exact Finset.sum_congr rfl fun index hindex =>
      hperIndex index hindex
  rw [hsum]
  simp only [Finset.sum_const, nsmul_eq_mul]
  simp only [Fintype.card_prod, Nat.cast_mul]
  field_simp

/-- Exact terminal Markov bound for the affine hash.  Unlike the level
variance estimate, this uses only one-output uniformity. -/
theorem affineCell_nonempty_le
    {Index 𝔽 : Type} [Field 𝔽] [Fintype 𝔽]
    [DecidableEq Index] [DecidableEq 𝔽]
    (active : Finset Index) (label : Index → 𝔽) (cell : Finset 𝔽) :
    booleanMean (fun seed : 𝔽 × 𝔽 =>
      decide (0 < affineCellCount active label cell seed)) ≤
      active.card * (cell.card / Fintype.card 𝔽 : ℝ) := by
  letI : Nonempty (𝔽 × 𝔽) := ⟨(0, 0)⟩
  calc
    booleanMean (fun seed : 𝔽 × 𝔽 =>
        decide (0 < affineCellCount active label cell seed)) ≤
        realMean (fun seed : 𝔽 × 𝔽 =>
          (affineCellCount active label cell seed : ℝ)) :=
      booleanMean_positiveNat_le_realMean
        (affineCellCount active label cell)
    _ = active.card * (cell.card / Fintype.card 𝔽 : ℝ) :=
      realMean_affineCellCount active label cell

theorem affineCell_terminalBound
    {Index 𝔽 : Type} [Field 𝔽] [Fintype 𝔽]
    [DecidableEq Index] [DecidableEq 𝔽]
    (active : Finset Index) (label : Index → 𝔽) (cell : Finset 𝔽)
    (level activeBound : ℕ)
    (hactive : active.card ≤ activeBound)
    (hdensity :
      (cell.card : ℝ) / Fintype.card 𝔽 ≤ 1 / (2 : ℝ) ^ level) :
    booleanMean (fun seed : 𝔽 × 𝔽 =>
      decide (0 < affineCellCount active label cell seed)) ≤
      (activeBound : ℝ) / (2 : ℝ) ^ level := by
  calc
    booleanMean (fun seed : 𝔽 × 𝔽 =>
        decide (0 < affineCellCount active label cell seed)) ≤
        (active.card : ℝ) *
          ((cell.card : ℝ) / Fintype.card 𝔽) :=
      affineCell_nonempty_le active label cell
    _ ≤ (activeBound : ℝ) * (1 / (2 : ℝ) ^ level) := by
      apply mul_le_mul
      · exact_mod_cast hactive
      · exact hdensity
      · positivity
      · positivity
    _ = (activeBound : ℝ) / (2 : ℝ) ^ level := by ring

end NearCubicWires.SupplierList
