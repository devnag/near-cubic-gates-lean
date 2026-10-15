import Proof.Foundations.OuterPCPRecovery

/-!
# Source-only exact-width envelope for the outer projection PCP

The executable PCP may report an irregular native address width.  Its imported
proof-count bound nevertheless gives one canonical logarithmic width depending
only on the source length and fixed source constants.  Padding to this envelope
makes the recovery schedule branch-independent without assuming monotonicity of
the runner's decoded output.
-/

namespace NearCubicWires.ProjectionWidthEnvelope

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.SourceInterfaces

def widthBudget
    {bound : ℕ → ℕ} {source : ExecutableRefuterSource bound}
    (outer : HierarchyOuterPCP source) (sourceLength : ℕ) : ℕ :=
  outer.pcp.shape.coefficient * bound sourceLength *
    logScale (bound sourceLength) ^ outer.proofExponent

/-- The least binary logarithmic envelope justified by the source's explicit
proof-count budget. -/
def widthEnvelope
    {bound : ℕ → ℕ} {source : ExecutableRefuterSource bound}
    (outer : HierarchyOuterPCP source) (sourceLength : ℕ) : ℕ :=
  Nat.log 2 (widthBudget outer sourceLength)

theorem nativeWidth_le_widthEnvelope
    {bound : ℕ → ℕ} {source : ExecutableRefuterSource bound}
    (outer : HierarchyOuterPCP source) (sourceLength : ℕ) :
    outer.pcp.nativeWidth sourceLength ≤
      widthEnvelope outer sourceLength := by
  apply Nat.le_log_of_pow_le (by omega)
  exact outer.proofSizeBound sourceLength

theorem widthBudget_positive
    {bound : ℕ → ℕ} {source : ExecutableRefuterSource bound}
    (outer : HierarchyOuterPCP source) (sourceLength : ℕ) :
    0 < widthBudget outer sourceLength := by
  have hproof := outer.proofSizeBound sourceLength
  have hpow : 0 < 2 ^ outer.pcp.nativeWidth sourceLength := by positivity
  exact hpow.trans_le hproof

theorem two_pow_widthEnvelope_le_budget
    {bound : ℕ → ℕ} {source : ExecutableRefuterSource bound}
    (outer : HierarchyOuterPCP source) (sourceLength : ℕ) :
    2 ^ widthEnvelope outer sourceLength ≤
      widthBudget outer sourceLength := by
  exact Nat.pow_log_le_self 2 (widthBudget_positive outer sourceLength).ne'

theorem logScale_positive (value : ℕ) : 0 < logScale value := by
  exact Nat.clog_pos (by omega) (by omega)

theorem logScale_le_add_two (value : ℕ) :
    logScale value ≤ value + 2 := by
  unfold logScale
  exact Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)

theorem bound_le_widthBudget
    {bound : ℕ → ℕ} {source : ExecutableRefuterSource bound}
    (outer : HierarchyOuterPCP source) (sourceLength : ℕ) :
    bound sourceLength ≤ widthBudget outer sourceLength := by
  unfold widthBudget
  have hcoefficient : 1 ≤ outer.pcp.shape.coefficient :=
    outer.pcp.shape.coefficientPositive
  have hlog : 1 ≤ logScale (bound sourceLength) :=
    logScale_positive _
  have hpower :
      1 ≤ logScale (bound sourceLength) ^ outer.proofExponent :=
    Nat.one_le_pow outer.proofExponent _ (logScale_positive _)
  calc
    bound sourceLength = 1 * bound sourceLength * 1 := by simp
    _ ≤ outer.pcp.shape.coefficient * bound sourceLength *
          logScale (bound sourceLength) ^ outer.proofExponent := by
      gcongr

theorem logScale_mono {left right : ℕ} (hle : left ≤ right) :
    logScale left ≤ logScale right := by
  apply Nat.clog_mono_right 2
  omega

theorem widthBudget_mono
    {bound : ℕ → ℕ} {source : ExecutableRefuterSource bound}
    (outer : HierarchyOuterPCP source) (hbound : Monotone bound) :
    Monotone (widthBudget outer) := by
  intro left right hle
  unfold widthBudget
  have hclock := hbound hle
  have hlog := logScale_mono hclock
  gcongr

theorem widthEnvelope_mono
    {bound : ℕ → ℕ} {source : ExecutableRefuterSource bound}
    (outer : HierarchyOuterPCP source) (hbound : Monotone bound) :
    Monotone (widthEnvelope outer) := by
  intro left right hle
  apply Nat.log_mono_right
  exact widthBudget_mono outer hbound hle

theorem pairClock_widthEnvelope_mono
    {depth : ℕ} {source : ExecutableRefuterSource (pairClock depth)}
    (outer : HierarchyOuterPCP source) :
    Monotone (widthEnvelope outer) := by
  apply widthEnvelope_mono outer
  intro left right hle
  simpa only [pairClock] using pairIter_mono_value depth hle

/-- Recovery enumerates source lengths `2^s`; the canonical exact width remains
monotone after that fixed enumeration. -/
theorem exponentialSource_widthEnvelope_mono
    {depth : ℕ} {source : ExecutableRefuterSource (pairClock depth)}
    (outer : HierarchyOuterPCP source) :
    Monotone (fun exponent => widthEnvelope outer (2 ^ exponent)) := by
  intro left right hle
  apply pairClock_widthEnvelope_mono outer
  exact Nat.pow_le_pow_right (by omega) hle

theorem sourceExponent_le_widthEnvelope
    {depth exponent : ℕ}
    {source : ExecutableRefuterSource (pairClock depth)}
    (outer : HierarchyOuterPCP source) :
    exponent ≤ widthEnvelope outer (2 ^ exponent) := by
  apply Nat.le_log_of_pow_le (by omega)
  exact
    (value_le_pairIter depth (2 ^ exponent)).trans
      (bound_le_widthBudget outer (2 ^ exponent))

/-- A pairing clock evaluated on a binary source length still has a binary
description whose exponent grows linearly in the source exponent. -/
theorem pairClock_two_pow_le
    (depth exponent : ℕ) :
    pairClock depth (2 ^ exponent) ≤
      2 ^ ((exponent + 1) * 2 ^ depth) := by
  have hbase :
      2 ^ exponent + 1 ≤ 2 ^ (exponent + 1) := by
    have hone : 1 ≤ 2 ^ exponent :=
      Nat.one_le_pow exponent 2 (by omega)
    calc
      2 ^ exponent + 1 ≤ 2 ^ exponent + 2 ^ exponent := by omega
      _ = 2 ^ (exponent + 1) := by
        rw [Nat.pow_succ]
        ring
  calc
    pairClock depth (2 ^ exponent) ≤
        pairClock depth (2 ^ exponent) + 1 := by omega
    _ ≤ (2 ^ exponent + 1) ^ (2 ^ depth) :=
      pairIter_add_one_le_pow depth (2 ^ exponent)
    _ ≤ (2 ^ (exponent + 1)) ^ (2 ^ depth) :=
      Nat.pow_le_pow_left hbase _
    _ = 2 ^ ((exponent + 1) * 2 ^ depth) := by
      rw [pow_mul]

theorem pairClock_two_pow_add_two_le
    (depth exponent : ℕ) :
    pairClock depth (2 ^ exponent) + 2 ≤
      2 ^ (((exponent + 1) * 2 ^ depth) + 2) := by
  let clockExponent := (exponent + 1) * 2 ^ depth
  have hclock :
      pairClock depth (2 ^ exponent) ≤ 2 ^ clockExponent := by
    simpa [clockExponent] using pairClock_two_pow_le depth exponent
  have hone : 1 ≤ 2 ^ clockExponent :=
    Nat.one_le_pow clockExponent 2 (by omega)
  calc
    pairClock depth (2 ^ exponent) + 2 ≤
        2 ^ clockExponent + 2 := by omega
    _ ≤ 4 * 2 ^ clockExponent := by omega
    _ = 2 ^ (clockExponent + 2) := by
      rw [pow_add]
      norm_num
      ring
    _ = 2 ^ (((exponent + 1) * 2 ^ depth) + 2) := by
      rfl

/-- One fixed coefficient absorbs every source-independent term in the padded
PCP width.  Keeping it explicit lets the recovery schedule use a single
polynomial envelope rather than a second asymptotic witness. -/
def widthLinearCoefficient
    {depth : ℕ} {source : ExecutableRefuterSource (pairClock depth)}
    (outer : HierarchyOuterPCP source) (scale : ℕ) : ℕ :=
  RecoveryPipeline.coefficientExponent outer.pcp.shape.coefficient +
    ((scale + 1) * 2 ^ depth) * (outer.proofExponent + 1) +
    2 * outer.proofExponent + 1

theorem widthLinearCoefficient_positive
    {depth : ℕ} {source : ExecutableRefuterSource (pairClock depth)}
    (outer : HierarchyOuterPCP source) (scale : ℕ) :
    0 < widthLinearCoefficient outer scale := by
  unfold widthLinearCoefficient
  omega

/-- Along source lengths `2^(scale*(s+1))`, the exact padded PCP width is at
most linear in `s+1`.  This is the quantitative bridge from the imported
proof-size bound to the smooth polynomial target-length schedule. -/
theorem widthEnvelope_exponential_le_linear
    {depth : ℕ} {source : ExecutableRefuterSource (pairClock depth)}
    (outer : HierarchyOuterPCP source) (scale sourceIndex : ℕ) :
    widthEnvelope outer (2 ^ (scale * (sourceIndex + 1))) ≤
      widthLinearCoefficient outer scale * (sourceIndex + 1) := by
  let unit := sourceIndex + 1
  let exponent := scale * unit
  let clockExponent := (exponent + 1) * 2 ^ depth
  let coefficientExponent :=
    RecoveryPipeline.coefficientExponent outer.pcp.shape.coefficient
  let linearRate := (scale + 1) * 2 ^ depth
  have hunit : 1 ≤ unit := by
    simp [unit]
  have hexponent :
      exponent + 1 ≤ (scale + 1) * unit := by
    dsimp only [exponent]
    calc
      scale * unit + 1 ≤ scale * unit + unit := by omega
      _ = (scale + 1) * unit := by ring
  have hclockExponent :
      clockExponent ≤ linearRate * unit := by
    dsimp only [clockExponent, linearRate]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      Nat.mul_le_mul_right (2 ^ depth) hexponent
  have hcoefficient :
      outer.pcp.shape.coefficient ≤ 2 ^ coefficientExponent := by
    simpa [coefficientExponent] using
      RecoveryPipeline.coefficient_le_two_pow
        outer.pcp.shape.coefficient
  have hclock :
      pairClock depth (2 ^ exponent) ≤ 2 ^ clockExponent := by
    simpa [clockExponent] using pairClock_two_pow_le depth exponent
  have hlogScale :
      logScale (pairClock depth (2 ^ exponent)) ≤
        2 ^ (clockExponent + 2) := by
    exact
      (logScale_le_add_two (pairClock depth (2 ^ exponent))).trans
        (by simpa [clockExponent] using
          pairClock_two_pow_add_two_le depth exponent)
  have hbudget :
      widthBudget outer (2 ^ exponent) ≤
        2 ^ (coefficientExponent + clockExponent +
          (clockExponent + 2) * outer.proofExponent) := by
    unfold widthBudget
    calc
      outer.pcp.shape.coefficient * pairClock depth (2 ^ exponent) *
            logScale (pairClock depth (2 ^ exponent)) ^
              outer.proofExponent ≤
          2 ^ coefficientExponent * 2 ^ clockExponent *
            (2 ^ (clockExponent + 2)) ^ outer.proofExponent := by
        gcongr
      _ = 2 ^ (coefficientExponent + clockExponent +
          (clockExponent + 2) * outer.proofExponent) := by
        simp only [← pow_add, ← pow_mul]
  have hexponentBound :
      coefficientExponent + clockExponent +
          (clockExponent + 2) * outer.proofExponent ≤
        widthLinearCoefficient outer scale * unit := by
    have hfixed :
        coefficientExponent + 2 * outer.proofExponent ≤
          (coefficientExponent + 2 * outer.proofExponent) * unit := by
      calc
        coefficientExponent + 2 * outer.proofExponent =
            (coefficientExponent + 2 * outer.proofExponent) * 1 := by ring
        _ ≤ (coefficientExponent + 2 * outer.proofExponent) * unit := by
          gcongr
    calc
      coefficientExponent + clockExponent +
            (clockExponent + 2) * outer.proofExponent ≤
          coefficientExponent + linearRate * unit +
            (linearRate * unit + 2) * outer.proofExponent := by
        gcongr
      _ =
          (coefficientExponent + 2 * outer.proofExponent) +
            (linearRate * (outer.proofExponent + 1)) * unit := by
        ring
      _ ≤
          (coefficientExponent + 2 * outer.proofExponent) * unit +
            (linearRate * (outer.proofExponent + 1)) * unit := by
        gcongr
      _ =
          (coefficientExponent + 2 * outer.proofExponent +
            linearRate * (outer.proofExponent + 1)) * unit := by
        ring
      _ ≤ widthLinearCoefficient outer scale * unit := by
        apply Nat.mul_le_mul_right
        unfold widthLinearCoefficient
        dsimp only [coefficientExponent, linearRate]
        omega
  have hbudgetPower :
      widthBudget outer (2 ^ exponent) ≤
        2 ^ (widthLinearCoefficient outer scale * unit) :=
    hbudget.trans
      (Nat.pow_le_pow_right (by omega) hexponentBound)
  have hwidth :
      widthEnvelope outer (2 ^ exponent) ≤
        widthLinearCoefficient outer scale * unit := by
    unfold widthEnvelope
    exact
      (Nat.log_le_clog 2 _).trans
        (Nat.clog_le_of_le_pow hbudgetPower)
  simpa [unit, exponent] using hwidth

theorem widthEnvelope_exponential_polynomiallyBounded
    {depth : ℕ} {source : ExecutableRefuterSource (pairClock depth)}
    (outer : HierarchyOuterPCP source) (scale : ℕ) :
    PolynomiallyBounded
      (fun sourceIndex =>
        widthEnvelope outer (2 ^ (scale * (sourceIndex + 1)))) := by
  refine
    ⟨widthLinearCoefficient outer scale, 1,
      widthLinearCoefficient_positive outer scale, ?_⟩
  intro sourceIndex
  simpa only [pow_one] using
    widthEnvelope_exponential_le_linear outer scale sourceIndex

end NearCubicWires.ProjectionWidthEnvelope
