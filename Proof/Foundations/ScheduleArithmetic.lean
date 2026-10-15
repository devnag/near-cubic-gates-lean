import Proof.Foundations.RecoveryPipeline

/-!
# First-crossing arithmetic for executable recovery schedules

The recovery program searches a fixed increasing sequence of source instances
for the first core whose double exceeds the requested target.  This module
owns the semantic arithmetic of that search.  It is deliberately independent
of PCP and refuter objects: the downstream executable selector must prove that
its decoded output is exactly `firstCrossingSelection`.
-/

namespace NearCubicWires.ScheduleArithmetic

open NearCubicWires.RecoveryPipeline

/-- Sufficient facts about one source-indexed core-width sequence.  Crossing is
stated in offsets from `sourceOnset`, so the first valid source need not be
zero.  The adjacent bound is the manuscript's one-sixth jump condition in the
division-free form consumed by `BoundedJumpSelection`. -/
structure FirstCrossingData (coreArity : ℕ → ℕ) (target : ℕ) where
  sourceOnset : ℕ
  monotone : Monotone coreArity
  belowAtOnset : 2 * coreArity sourceOnset ≤ target
  crossingExists :
    ∃ offset, target < 2 * coreArity (sourceOnset + offset)
  adjacentJump : ∀ source, sourceOnset ≤ source →
    2 * coreArity source ≤ target →
    6 * coreArity (source + 1) ≤
      6 * coreArity source + target

/-- The least offset at which the increasing core sequence crosses half the
target. -/
def FirstCrossingData.nextOffset
    {coreArity : ℕ → ℕ} {target : ℕ}
    (data : FirstCrossingData coreArity target) : ℕ :=
  Nat.find data.crossingExists

/-- The preceding offset.  `belowAtOnset` proves that `nextOffset` is positive,
so this truncated subtraction is an actual predecessor. -/
def FirstCrossingData.sourceOffset
    {coreArity : ℕ → ℕ} {target : ℕ}
    (data : FirstCrossingData coreArity target) : ℕ :=
  data.nextOffset - 1

def FirstCrossingData.source
    {coreArity : ℕ → ℕ} {target : ℕ}
    (data : FirstCrossingData coreArity target) : ℕ :=
  data.sourceOnset + data.sourceOffset

def FirstCrossingData.nextSource
    {coreArity : ℕ → ℕ} {target : ℕ}
    (data : FirstCrossingData coreArity target) : ℕ :=
  data.sourceOnset + data.nextOffset

/-- The canonical tuple that the fixed selector program must emit. -/
def firstCrossingSelection
    {coreArity : ℕ → ℕ} {target : ℕ}
    (data : FirstCrossingData coreArity target) :
    ExecutableScheduleSelection where
  source := data.source
  nextSource := data.nextSource
  core := coreArity data.source
  nextCore := coreArity data.nextSource

theorem FirstCrossingData.crossesAtNextOffset
    {coreArity : ℕ → ℕ} {target : ℕ}
    (data : FirstCrossingData coreArity target) :
    target <
      2 * coreArity (data.sourceOnset + data.nextOffset) :=
  Nat.find_spec data.crossingExists

theorem FirstCrossingData.nextOffset_positive
    {coreArity : ℕ → ℕ} {target : ℕ}
    (data : FirstCrossingData coreArity target) :
    0 < data.nextOffset := by
  by_contra hnot
  have hzero : data.nextOffset = 0 := by omega
  have hcross := data.crossesAtNextOffset
  have hbelow := data.belowAtOnset
  rw [hzero, Nat.add_zero] at hcross
  omega

theorem FirstCrossingData.sourceOffset_lt_nextOffset
    {coreArity : ℕ → ℕ} {target : ℕ}
    (data : FirstCrossingData coreArity target) :
    data.sourceOffset < data.nextOffset := by
  exact Nat.sub_lt data.nextOffset_positive (by omega)

theorem FirstCrossingData.sourceOffset_succ
    {coreArity : ℕ → ℕ} {target : ℕ}
    (data : FirstCrossingData coreArity target) :
    data.sourceOffset + 1 = data.nextOffset := by
  exact Nat.sub_add_cancel (by
    exact data.nextOffset_positive)

theorem FirstCrossingData.source_succ
    {coreArity : ℕ → ℕ} {target : ℕ}
    (data : FirstCrossingData coreArity target) :
    data.source + 1 = data.nextSource := by
  unfold FirstCrossingData.source FirstCrossingData.nextSource
  rw [← data.sourceOffset_succ]
  omega

theorem FirstCrossingData.sourceBeforeNext
    {coreArity : ℕ → ℕ} {target : ℕ}
    (data : FirstCrossingData coreArity target) :
    data.source < data.nextSource := by
  rw [← data.source_succ]
  omega

theorem FirstCrossingData.sourceAtOrAfterOnset
    {coreArity : ℕ → ℕ} {target : ℕ}
    (data : FirstCrossingData coreArity target) :
    data.sourceOnset ≤ data.source := by
  simp [FirstCrossingData.source]

/-- Minimality of the first crossing makes its predecessor genuinely
below-half.  This is stronger than the `core ≤ target` field ultimately
exported by the bounded-jump schedule. -/
theorem FirstCrossingData.sourceBelowHalf
    {coreArity : ℕ → ℕ} {target : ℕ}
    (data : FirstCrossingData coreArity target) :
    2 * coreArity data.source ≤ target := by
  have hminimal :
      ¬target <
        2 * coreArity (data.sourceOnset + data.sourceOffset) :=
    Nat.find_min data.crossingExists data.sourceOffset_lt_nextOffset
  simpa [FirstCrossingData.source] using Nat.le_of_not_gt hminimal

theorem FirstCrossingData.coreAtMostTarget
    {coreArity : ℕ → ℕ} {target : ℕ}
    (data : FirstCrossingData coreArity target) :
    coreArity data.source ≤ target := by
  have := data.sourceBelowHalf
  omega

theorem FirstCrossingData.crossesHalf
    {coreArity : ℕ → ℕ} {target : ℕ}
    (data : FirstCrossingData coreArity target) :
    target < 2 * coreArity data.nextSource := by
  simpa [FirstCrossingData.nextSource] using data.crossesAtNextOffset

theorem FirstCrossingData.jumpAtMostSixth
    {coreArity : ℕ → ℕ} {target : ℕ}
    (data : FirstCrossingData coreArity target) :
    6 * coreArity data.nextSource ≤
      6 * coreArity data.source + target := by
  rw [← data.source_succ]
  exact data.adjacentJump data.source data.sourceAtOrAfterOnset
    data.sourceBelowHalf

/-- Every valid source before the first crossing is below half.  This exposes
the exact maximality fact used when reviewing a selector implementation. -/
theorem FirstCrossingData.belowHalf_of_beforeNext
    {coreArity : ℕ → ℕ} {target candidate : ℕ}
    (data : FirstCrossingData coreArity target)
    (honset : data.sourceOnset ≤ candidate)
    (hbefore : candidate < data.nextSource) :
    2 * coreArity candidate ≤ target := by
  let offset := candidate - data.sourceOnset
  have hcandidate :
      data.sourceOnset + offset = candidate := by
    exact Nat.add_sub_of_le honset
  have hoffset : offset < data.nextOffset := by
    unfold FirstCrossingData.nextSource at hbefore
    omega
  have hminimal :
      ¬target <
        2 * coreArity (data.sourceOnset + offset) :=
    Nat.find_min data.crossingExists hoffset
  rw [hcandidate] at hminimal
  exact Nat.le_of_not_gt hminimal

/-- Monotonicity makes the selected predecessor the greatest source at or
after the onset whose core remains below half. -/
theorem FirstCrossingData.candidate_le_source_of_belowHalf
    {coreArity : ℕ → ℕ} {target candidate : ℕ}
    (data : FirstCrossingData coreArity target)
    (hbelow : 2 * coreArity candidate ≤ target) :
    candidate ≤ data.source := by
  by_contra hnot
  have hnext : data.nextSource ≤ candidate := by
    rw [← data.source_succ]
    omega
  have hcore :
      coreArity data.nextSource ≤ coreArity candidate :=
    data.monotone hnext
  have hcross := data.crossesHalf
  omega

/-- All four arithmetic fields exported to the executable recovery schedule,
plus the source-index ordering field. -/
theorem firstCrossingSelection_valid
    {coreArity : ℕ → ℕ} {target : ℕ}
    (data : FirstCrossingData coreArity target) :
    let selection := firstCrossingSelection data
    selection.source < selection.nextSource ∧
      selection.core ≤ target ∧
      target < 2 * selection.nextCore ∧
      6 * selection.nextCore ≤ 6 * selection.core + target := by
  exact
    ⟨data.sourceBeforeNext, data.coreAtMostTarget,
      data.crossesHalf, data.jumpAtMostSixth⟩

/-- Forget source indices after checking them and obtain the exact padding
object consumed by the recovery pipeline. -/
def FirstCrossingData.toBoundedJumpSelection
    {coreArity : ℕ → ℕ} {target : ℕ}
    (data : FirstCrossingData coreArity target) :
    BoundedJumpSelection target where
  core := coreArity data.source
  next := coreArity data.nextSource
  coreAtMostTarget := data.coreAtMostTarget
  crossesHalf := data.crossesHalf
  jumpAtMostSixth := data.jumpAtMostSixth

end NearCubicWires.ScheduleArithmetic
