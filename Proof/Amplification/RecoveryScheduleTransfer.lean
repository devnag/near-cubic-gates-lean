import Proof.Foundations.RecoveryScheduleEnvelope
import Proof.Foundations.WireScaleTransfer

/-!
# Tight recovery schedule cap transfer

The source reindexing first pads each raw recovery core to the exact linear
core consumed by the executable selector.  These lemmas pay that one
constant-factor padding loss at the physical wire scale.  The later
target-length selector still owns its independent factor-three loss.
-/

namespace NearCubicWires.RecoveryScheduleTransfer

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.SourceInterfaces
open NearCubicWires.WireScaleTransfer

theorem inverseCoreWireScale_le_raw
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate scheduleIndex logExponent : ℕ)
    (hrate : 1 ≤ rate)
    (coefficient : ℝ) (hcoefficient : 0 ≤ coefficient) :
    wireScale
        (coefficient /
          (inverseCorePaddingFactor
            outer pcppSource requiredDegree rate : ℝ) ^ 3)
        logExponent
        ((inverseCoreEnvelope outer pcppSource
          requiredDegree rate).coreArity scheduleIndex) ≤
      wireScale coefficient logExponent
        (inverseScheduledRawCoreArity
          outer pcppSource requiredDegree rate scheduleIndex) := by
  apply wireScale_shrink_cube hcoefficient
    (inverseCorePaddingFactor
      outer pcppSource requiredDegree rate)
    logExponent
    (inverseCorePaddingFactor_positive
      outer pcppSource requiredDegree rate)
  · exact
      (inverseCoreEnvelope outer pcppSource
        requiredDegree rate).rawArity_le_coreArity scheduleIndex
  · exact inverseCoreEnvelope_le_paddingFactor_mul_raw
      outer pcppSource requiredDegree rate scheduleIndex hrate

theorem fixedCoreWireScale_le_raw
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree rate sourceIndex logExponent : ℕ)
    (coefficient : ℝ) (hcoefficient : 0 ≤ coefficient) :
    wireScale
        (coefficient /
          (fixedCorePaddingFactor
            outer pcppSource requiredDegree : ℝ) ^ 3)
        logExponent
        ((fixedCoreEnvelope outer pcppSource
          requiredDegree rate).coreArity sourceIndex) ≤
      wireScale coefficient logExponent
        (fixedRawCoreArity
          outer pcppSource requiredDegree rate sourceIndex) := by
  apply wireScale_shrink_cube hcoefficient
    (fixedCorePaddingFactor outer pcppSource requiredDegree)
    logExponent
    (fixedCorePaddingFactor_positive
      outer pcppSource requiredDegree)
  · exact
      (fixedCoreEnvelope outer pcppSource
        requiredDegree rate).rawArity_le_coreArity sourceIndex
  · exact fixedCoreEnvelope_le_paddingFactor_mul_raw
      outer pcppSource requiredDegree rate sourceIndex

end NearCubicWires.RecoveryScheduleTransfer
