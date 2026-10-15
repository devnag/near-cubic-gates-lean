import Proof.Foundations.ScheduledRecovery

/-!
# Case-one schedule ledger

The STV branch receives the pairing-clock oracle bound selected by the common
outer split.  This file records the two quantitative consequences needed by
closed recovery assembly: a chosen polynomial power survives the STV integer
root, and the corresponding STV advantage is at most the matching inverse
power.  Both facts are derived from the exact pairing-clock lower bound.
-/

namespace NearCubicWires.CaseOneScheduleLedger

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces

theorem oraclePower_le_stvSize
    (amplifier : AmplifierWitness)
    (requiredDegree power width : ℕ)
    (hwidth : 0 < width)
    (hdegree :
      power * amplifier.stvExponent ≤ requiredDegree) :
    width ^ power ≤
      integerFloorRoot amplifier.stvExponent
        (oracleSizeBound requiredDegree width) := by
  apply pow_le_integerFloorRoot_of_mul_le
    (lt_of_lt_of_le (by omega) amplifier.stvExponentPositive)
    hwidth
  · exact hdegree.trans (requiredDegree_le_oracleDegree requiredDegree)
  · exact pow_twoPow_le_pairClock
      (oracleDepth requiredDegree) width

theorem oracleAdvantage_le_inversePower
    (amplifier : AmplifierWitness)
    (requiredDegree power width : ℕ)
    (hwidth : 0 < width)
    (hdegree :
      power * amplifier.stvExponent ≤ requiredDegree) :
    Real.rpow (oracleSizeBound requiredDegree width : ℝ)
        (-(1 : ℝ) / amplifier.stvExponent) ≤
      inversePolynomialAdvantage width (power : ℝ) := by
  have hstv : 0 < amplifier.stvExponent :=
    lt_of_lt_of_le (by omega) amplifier.stvExponentPositive
  have hexponent :
      power * amplifier.stvExponent ≤
        2 ^ oracleDepth requiredDegree :=
    hdegree.trans (requiredDegree_le_oracleDegree requiredDegree)
  have hpowerNat :
      width ^ (power * amplifier.stvExponent) ≤
        oracleSizeBound requiredDegree width := by
    unfold oracleSizeBound
    exact
      (Nat.pow_le_pow_right hwidth hexponent).trans
        (pow_twoPow_le_pairClock
          (oracleDepth requiredDegree) width)
  have hpowerReal :
      (width : ℝ) ^ (power * amplifier.stvExponent) ≤
        (oracleSizeBound requiredDegree width : ℝ) := by
    exact_mod_cast hpowerNat
  have hnegative :
      -(1 : ℝ) / amplifier.stvExponent ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  calc
    Real.rpow (oracleSizeBound requiredDegree width : ℝ)
          (-(1 : ℝ) / amplifier.stvExponent) ≤
        Real.rpow ((width : ℝ) ^ (power * amplifier.stvExponent))
          (-(1 : ℝ) / amplifier.stvExponent) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hpowerReal hnegative
    _ = Real.rpow (width : ℝ) (-(power : ℝ)) := by
      rw [← Real.rpow_natCast]
      push_cast
      calc
        Real.rpow
              (Real.rpow (width : ℝ)
                ((power : ℝ) * (amplifier.stvExponent : ℝ)))
              (-(1 : ℝ) / amplifier.stvExponent) =
            Real.rpow (width : ℝ)
              (((power : ℝ) * (amplifier.stvExponent : ℝ)) *
                (-(1 : ℝ) / amplifier.stvExponent)) :=
          (Real.rpow_mul (x := (width : ℝ)) (by positivity)
            ((power : ℝ) * (amplifier.stvExponent : ℝ))
            (-(1 : ℝ) / amplifier.stvExponent)).symm
        _ = Real.rpow (width : ℝ) (-(power : ℝ)) := by
          congr 1
          field_simp
    _ = inversePolynomialAdvantage width (power : ℝ) := by
      rfl

theorem ScheduledCaseOneData.hardCore_size_ge_power
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {amplifier : AmplifierWitness}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (data : ScheduledCaseOneData outer amplifier
      requiredDegree sourceIndex input)
    (hyes :
      source.hierarchyMachine.accepts (sourceLength sourceIndex) input)
    (power : ℕ)
    (hdegree :
      power * amplifier.stvExponent ≤ requiredDegree) :
    scheduledWidth outer sourceIndex ^ power ≤
      (hardCoreFromCaseOne (data.amplifierInput hyes)).size := by
  change
    scheduledWidth outer sourceIndex ^ power ≤
      integerFloorRoot amplifier.stvExponent
        (oracleSizeBound requiredDegree
          (scheduledWidth outer sourceIndex))
  exact oraclePower_le_stvSize amplifier requiredDegree power
    (scheduledWidth outer sourceIndex)
    (lt_of_lt_of_le Nat.zero_lt_one <|
      (by omega : 1 ≤ sourceIndex + 1).trans <|
        sourceIndex_succ_le_scheduledWidth outer sourceIndex)
    hdegree

theorem ScheduledCaseOneData.hardCore_advantage_le_inverseWidth
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {amplifier : AmplifierWitness}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (data : ScheduledCaseOneData outer amplifier
      requiredDegree sourceIndex input)
    (hyes :
      source.hierarchyMachine.accepts (sourceLength sourceIndex) input)
    (power : ℕ)
    (hdegree :
      power * amplifier.stvExponent ≤ requiredDegree) :
    (hardCoreFromCaseOne (data.amplifierInput hyes)).advantage ≤
      inversePolynomialAdvantage
        (scheduledWidth outer sourceIndex) (power : ℝ) := by
  change
    Real.rpow
        (oracleSizeBound requiredDegree
          (scheduledWidth outer sourceIndex) : ℝ)
        (-(1 : ℝ) / amplifier.stvExponent) ≤ _
  exact oracleAdvantage_le_inversePower amplifier requiredDegree power
    (scheduledWidth outer sourceIndex)
    (lt_of_lt_of_le Nat.zero_lt_one <|
      (by omega : 1 ≤ sourceIndex + 1).trans <|
        sourceIndex_succ_le_scheduledWidth outer sourceIndex)
    hdegree

/-- Natural exponents expose inverse-polynomial advantage as an ordinary
reciprocal, which makes comparisons depend only on an exact natural power
inequality. -/
theorem inversePolynomialAdvantage_natPower
    (base power : ℕ) (hbase : 0 < base) :
    inversePolynomialAdvantage base (power : ℝ) =
      1 / (base : ℝ) ^ power := by
  unfold inversePolynomialAdvantage
  calc
    Real.rpow (base : ℝ) (-(power : ℝ)) =
        (Real.rpow (base : ℝ) (power : ℝ))⁻¹ :=
      Real.rpow_neg (by positivity) _
    _ = ((base : ℝ) ^ power)⁻¹ := by
      congr 1
      exact Real.rpow_natCast (base : ℝ) power
    _ = 1 / (base : ℝ) ^ power := by rw [one_div]

/-- A larger natural denominator gives a smaller inverse-polynomial
advantage, even when the two sides use different natural exponents. -/
theorem inversePolynomialAdvantage_le_of_pow_le
    (base target basePower targetPower : ℕ)
    (hbase : 0 < base)
    (htarget : 0 < target)
    (hpower : target ^ targetPower ≤ base ^ basePower) :
    inversePolynomialAdvantage base (basePower : ℝ) ≤
      inversePolynomialAdvantage target (targetPower : ℝ) := by
  rw [inversePolynomialAdvantage_natPower base basePower hbase,
    inversePolynomialAdvantage_natPower target targetPower htarget]
  have hpowerReal :
      (target : ℝ) ^ targetPower ≤ (base : ℝ) ^ basePower := by
    exact_mod_cast hpower
  exact one_div_le_one_div_of_le (by positivity) hpowerReal

/-- Once the schedule has passed the displayed onset, one power of the exact
inverse-tier core costs at most two source-width powers plus one factor used
to absorb the fixed coefficient. -/
theorem inverseCore_power_le_scheduledWidth
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate scheduleIndex power : ℕ)
    (hready :
      inverseCaseOnePowerOnset
        outer pcppSource requiredDegree rate power ≤ scheduleIndex) :
    (inverseCoreEnvelope outer pcppSource requiredDegree rate).coreArity
          scheduleIndex ^ power ≤
      scheduledWidth outer (inverseSourceIndex scheduleIndex) ^
        (2 * power + 1) := by
  let factor :=
    inverseCaseOneWidthFactor outer pcppSource requiredDegree rate
  let sourceIndex := inverseSourceIndex scheduleIndex
  let width := scheduledWidth outer sourceIndex
  let core :=
    (inverseCoreEnvelope outer pcppSource requiredDegree rate).coreArity
      scheduleIndex
  have honset :=
    inverseCaseOnePowerOnset_ready
      outer pcppSource requiredDegree rate power scheduleIndex hready
  have hfactorPowerIndex : factor ^ power ≤ sourceIndex := by
    exact le_inverseSourceIndex_of_measure_le
      (factor ^ power) scheduleIndex honset
  have hfactorPowerWidth : factor ^ power ≤ width := by
    exact hfactorPowerIndex.trans <|
      (Nat.le_succ sourceIndex).trans <|
        sourceIndex_succ_le_scheduledWidth outer sourceIndex
  have hcore : core ≤ factor * width ^ 2 := by
    exact inverseCoreEnvelope_le_widthSquare
      outer pcppSource requiredDegree rate scheduleIndex
  calc
    core ^ power ≤ (factor * width ^ 2) ^ power :=
      Nat.pow_le_pow_left hcore power
    _ = factor ^ power * (width ^ 2) ^ power := by rw [mul_pow]
    _ ≤ width * (width ^ 2) ^ power :=
      Nat.mul_le_mul_right ((width ^ 2) ^ power) hfactorPowerWidth
    _ = width ^ (2 * power + 1) := by
      rw [← pow_mul]
      simp only [pow_succ, Nat.mul_comm]

/-- The fixed-copy tier is linear in source width, so after its explicit
coefficient onset the corresponding loss is only one extra width power. -/
theorem fixedCore_power_le_scheduledWidth
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate sourceIndex power : ℕ)
    (hready :
      fixedCaseOnePowerOnset
        outer pcppSource requiredDegree rate power ≤ sourceIndex) :
    (fixedCoreEnvelope outer pcppSource requiredDegree rate).coreArity
          sourceIndex ^ power ≤
      scheduledWidth outer sourceIndex ^ (power + 1) := by
  let factor :=
    fixedCaseOneWidthFactor outer pcppSource requiredDegree rate
  let width := scheduledWidth outer sourceIndex
  let core :=
    (fixedCoreEnvelope outer pcppSource requiredDegree rate).coreArity
      sourceIndex
  have honset :=
    fixedCaseOnePowerOnset_ready
      outer pcppSource requiredDegree rate power sourceIndex hready
  have hfactorPowerWidth : factor ^ power ≤ width :=
    honset.trans <| sourceIndex_succ_le_scheduledWidth outer sourceIndex
  have hcore : core ≤ factor * width := by
    exact fixedCoreEnvelope_le_width
      outer pcppSource requiredDegree rate sourceIndex
  calc
    core ^ power ≤ (factor * width) ^ power :=
      Nat.pow_le_pow_left hcore power
    _ = factor ^ power * width ^ power := by rw [mul_pow]
    _ ≤ width * width ^ power :=
      Nat.mul_le_mul_right (width ^ power) hfactorPowerWidth
    _ = width ^ (power + 1) := by
      simp only [pow_succ, Nat.mul_comm]

/-- The inverse-tier hard-core size cap dominates the requested power of the
exact selected core after the same explicit onset. -/
theorem ScheduledCaseOneData.hardCore_size_ge_inverseCorePower
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {amplifier : AmplifierWitness}
    {pcppSource : UniformPointwisePCPPSource}
    {requiredDegree rate scheduleIndex power : ℕ}
    {input :
      BitInput (sourceLength (inverseSourceIndex scheduleIndex))}
    (data : ScheduledCaseOneData outer amplifier requiredDegree
      (inverseSourceIndex scheduleIndex) input)
    (hyes :
      source.hierarchyMachine.accepts
        (sourceLength (inverseSourceIndex scheduleIndex)) input)
    (hready :
      inverseCaseOnePowerOnset
        outer pcppSource requiredDegree rate power ≤ scheduleIndex)
    (hdegree :
      (2 * power + 1) * amplifier.stvExponent ≤ requiredDegree) :
    (inverseCoreEnvelope outer pcppSource requiredDegree rate).coreArity
          scheduleIndex ^ power ≤
      (hardCoreFromCaseOne (data.amplifierInput hyes)).size := by
  exact
    (inverseCore_power_le_scheduledWidth
      outer pcppSource requiredDegree rate scheduleIndex power hready).trans <|
      NearCubicWires.CaseOneScheduleLedger.ScheduledCaseOneData.hardCore_size_ge_power
        data hyes (2 * power + 1) hdegree

/-- The fixed-tier hard-core size cap has the corresponding sharper
exact-selected-core bound. -/
theorem ScheduledCaseOneData.hardCore_size_ge_fixedCorePower
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {amplifier : AmplifierWitness}
    {pcppSource : UniformPointwisePCPPSource}
    {requiredDegree rate sourceIndex power : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (data : ScheduledCaseOneData outer amplifier
      requiredDegree sourceIndex input)
    (hyes :
      source.hierarchyMachine.accepts (sourceLength sourceIndex) input)
    (hready :
      fixedCaseOnePowerOnset
        outer pcppSource requiredDegree rate power ≤ sourceIndex)
    (hdegree :
      (power + 1) * amplifier.stvExponent ≤ requiredDegree) :
    (fixedCoreEnvelope outer pcppSource requiredDegree rate).coreArity
          sourceIndex ^ power ≤
      (hardCoreFromCaseOne (data.amplifierInput hyes)).size := by
  exact
    (fixedCore_power_le_scheduledWidth
      outer pcppSource requiredDegree rate sourceIndex power hready).trans <|
      NearCubicWires.CaseOneScheduleLedger.ScheduledCaseOneData.hardCore_size_ge_power
        data hyes (power + 1) hdegree

/-- The inverse-tier STV reserve is stated against the exact selected core,
not merely the upstream source width. -/
theorem ScheduledCaseOneData.hardCore_advantage_le_inverseCore
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {amplifier : AmplifierWitness}
    {pcppSource : UniformPointwisePCPPSource}
    {requiredDegree rate scheduleIndex power : ℕ}
    {input :
      BitInput (sourceLength (inverseSourceIndex scheduleIndex))}
    (data : ScheduledCaseOneData outer amplifier requiredDegree
      (inverseSourceIndex scheduleIndex) input)
    (hyes :
      source.hierarchyMachine.accepts
        (sourceLength (inverseSourceIndex scheduleIndex)) input)
    (hready :
      inverseCaseOnePowerOnset
        outer pcppSource requiredDegree rate power ≤ scheduleIndex)
    (hdegree :
      (2 * power + 1) * amplifier.stvExponent ≤ requiredDegree) :
    (hardCoreFromCaseOne (data.amplifierInput hyes)).advantage ≤
      inversePolynomialAdvantage
        ((inverseCoreEnvelope outer pcppSource requiredDegree rate).coreArity
          scheduleIndex)
        (power : ℝ) := by
  have hwidthPositive :
      0 < scheduledWidth outer (inverseSourceIndex scheduleIndex) :=
    lt_of_lt_of_le Nat.zero_lt_one <|
      (by omega : 1 ≤ inverseSourceIndex scheduleIndex + 1).trans <|
        sourceIndex_succ_le_scheduledWidth outer
          (inverseSourceIndex scheduleIndex)
  have hcorePositive :
      0 <
        (inverseCoreEnvelope outer pcppSource requiredDegree rate).coreArity
          scheduleIndex := by
    rw [inverseCoreEnvelope_coreArity]
    exact Nat.mul_pos
      (inverseTightCoreCoefficient_positive
        outer pcppSource requiredDegree rate)
      (by omega)
  exact
    (NearCubicWires.CaseOneScheduleLedger.ScheduledCaseOneData.hardCore_advantage_le_inverseWidth
      data hyes
        (2 * power + 1) hdegree).trans <|
      inversePolynomialAdvantage_le_of_pow_le
        (scheduledWidth outer (inverseSourceIndex scheduleIndex))
        ((inverseCoreEnvelope outer pcppSource requiredDegree rate).coreArity
          scheduleIndex)
        (2 * power + 1) power hwidthPositive hcorePositive <|
          inverseCore_power_le_scheduledWidth
            outer pcppSource requiredDegree rate scheduleIndex power hready

/-- The fixed-tier STV reserve has the analogous exact-core statement with
the sharper linear-schedule exponent loss. -/
theorem ScheduledCaseOneData.hardCore_advantage_le_fixedCore
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {amplifier : AmplifierWitness}
    {pcppSource : UniformPointwisePCPPSource}
    {requiredDegree rate sourceIndex power : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (data : ScheduledCaseOneData outer amplifier
      requiredDegree sourceIndex input)
    (hyes :
      source.hierarchyMachine.accepts (sourceLength sourceIndex) input)
    (hready :
      fixedCaseOnePowerOnset
        outer pcppSource requiredDegree rate power ≤ sourceIndex)
    (hdegree :
      (power + 1) * amplifier.stvExponent ≤ requiredDegree) :
    (hardCoreFromCaseOne (data.amplifierInput hyes)).advantage ≤
      inversePolynomialAdvantage
        ((fixedCoreEnvelope outer pcppSource requiredDegree rate).coreArity
          sourceIndex)
        (power : ℝ) := by
  have hwidthPositive : 0 < scheduledWidth outer sourceIndex :=
    lt_of_lt_of_le Nat.zero_lt_one <|
      (by omega : 1 ≤ sourceIndex + 1).trans <|
        sourceIndex_succ_le_scheduledWidth outer sourceIndex
  have hcorePositive :
      0 <
        (fixedCoreEnvelope outer pcppSource requiredDegree rate).coreArity
          sourceIndex := by
    rw [fixedCoreEnvelope_coreArity]
    exact Nat.mul_pos
      (fixedRawLinearCoefficient_positive
        outer pcppSource requiredDegree rate)
      (by omega)
  exact
    (NearCubicWires.CaseOneScheduleLedger.ScheduledCaseOneData.hardCore_advantage_le_inverseWidth
      data hyes
        (power + 1) hdegree).trans <|
      inversePolynomialAdvantage_le_of_pow_le
        (scheduledWidth outer sourceIndex)
        ((fixedCoreEnvelope outer pcppSource requiredDegree rate).coreArity
          sourceIndex)
        (power + 1) power hwidthPositive hcorePositive <|
          fixedCore_power_le_scheduledWidth
            outer pcppSource requiredDegree rate sourceIndex power hready

end NearCubicWires.CaseOneScheduleLedger
