import Proof.Hierarchy.HierarchyEncodeReady

/-! The literal adopted source dimensions at the already fixed dyadic U
clock reduce to polynomial arithmetic in its exponent. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.DimensionDyadic
open SourceInterfaces ExecutableInterfaces RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def factor (C p e : ℕ) := C*(e+1)^p

theorem logScale_pow (e : ℕ) (he : 1 ≤ e) : logScale (2^e)=e+1 := by
  have hp : 2 ≤ (2 : ℕ)^e := by
    simpa using Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) he
  have hlo : e < logScale (2^e) := (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by omega)
  have hhi : logScale (2^e) ≤ e+1 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_succ]
    omega
  omega

theorem bitLength_shift (a e : ℕ) (ha : 0<a) : natBitLength (2^e*a)=e+natBitLength a := by
  have hlo : 2^(e+Nat.log 2 a) ≤ 2^e*a := by
    rw [pow_add]
    exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 (Nat.ne_of_gt ha))
  have hhi : 2^e*a < 2^((e+Nat.log 2 a)+1) := by
    rw [Nat.add_assoc,pow_add]
    exact Nat.mul_lt_mul_of_pos_left (Nat.lt_pow_succ_log_self (by decide) a) (by positivity)
  have hlog := Nat.log_eq_of_pow_le_of_lt_pow hlo hhi
  dsimp only [natBitLength]
  rw [hlog]
  omega

theorem exponent_positive (N : ℕ) : 1 ≤ ClockEnvelope.exponent 23 5 N := by
  dsimp [ClockEnvelope.exponent]
  omega

theorem envelope_eq (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (N : ℕ) :
    Dimensions.envelope source N=2^ClockEnvelope.exponent 23 5 N*
      factor source.coefficient source.degrees.proofLog (ClockEnvelope.exponent 23 5 N) := by
  unfold Dimensions.envelope
  change source.coefficient*(2^ClockEnvelope.exponent 23 5 N)*
    logScale (2^ClockEnvelope.exponent 23 5 N)^source.degrees.proofLog=_
  rw [logScale_pow _ (exponent_positive N)]
  dsimp [factor]
  ring

theorem width_eq (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (N : ℕ) :
    Dimensions.width source N=ClockEnvelope.exponent 23 5 N+
      natBitLength (factor source.coefficient source.degrees.proofLog (ClockEnvelope.exponent 23 5 N)) := by
  unfold Dimensions.width
  rw [envelope_eq,bitLength_shift]
  have hc := source.coefficientPositive
  dsimp [factor]
  positivity

theorem queries_eq (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (N : ℕ) :
    Dimensions.queries source N=factor source.coefficient source.degrees.queries (Dimensions.width source N) := rfl

end NearCubicWires.RepairSource.ProjectionNormalization.DimensionDyadic
