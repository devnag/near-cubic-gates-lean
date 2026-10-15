import Proof.PCP.ProjectionNormalizationQueryBytes

/-! Exact length-only dimension choice for the one selected source witness.
The common width is the bit length of its actual proof-size envelope; no
maximum over inputs and no lower raw-width estimate are used. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Dimensions
open SourceInterfaces ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def envelope {v : OrdinaryVerifier} {T : ℕ → ℕ} (source : ProjectionSourceAlgorithm v T) (N : ℕ) :=
  source.coefficient*T N*logScale (T N)^source.degrees.proofLog
def width {v : OrdinaryVerifier} {T : ℕ → ℕ} (source : ProjectionSourceAlgorithm v T) (N : ℕ) :=
  natBitLength (envelope source N)
def queries {v : OrdinaryVerifier} {T : ℕ → ℕ} (source : ProjectionSourceAlgorithm v T) (N : ℕ) :=
  source.coefficient*(width source N+1)^source.degrees.queries

theorem envelope_positive {v : OrdinaryVerifier} {T : ℕ → ℕ} (source : ProjectionSourceAlgorithm v T)
    (r : InputRequest) (hr : 1≤r.1) : 0<envelope source r.1 := by
  have h := source.proofBound r hr
  have hp : 0<(2 : ℕ)^(source.output r).width := by positivity
  exact lt_of_lt_of_le hp h

theorem width_fits {v : OrdinaryVerifier} {T : ℕ → ℕ} (source : ProjectionSourceAlgorithm v T)
    (r : InputRequest) (hr : 1≤r.1) : (source.output r).width≤width source r.1 := by
  have hb : 2^(source.output r).width≤envelope source r.1 := source.proofBound r hr
  have he : envelope source r.1<2^width source r.1 := Nat.lt_pow_succ_log_self (by decide) _
  by_contra h
  have hp := Nat.pow_le_pow_right (by decide : 0<(2 : ℕ))
    (show width source r.1+1≤(source.output r).width by omega)
  have hw := Nat.pow_lt_pow_right (by decide : 1<(2 : ℕ))
    (show width source r.1<width source r.1+1 by omega)
  omega

theorem queries_fit {v : OrdinaryVerifier} {T : ℕ → ℕ} (source : ProjectionSourceAlgorithm v T)
    (r : InputRequest) (hr : 1≤r.1) : (source.output r).queries≤queries source r.1 := by
  exact (source.queryBound r hr).trans
    (Nat.mul_le_mul_left source.coefficient
      (Nat.pow_le_pow_left (Nat.add_le_add_right (width_fits source r hr) 1) _))

theorem proof_size {v : OrdinaryVerifier} {T : ℕ → ℕ} (source : ProjectionSourceAlgorithm v T)
    (r : InputRequest) (hr : 1≤r.1) : 2^width source r.1≤2*envelope source r.1 := by
  have hp := Nat.pow_log_le_self 2 (Nat.ne_of_gt (envelope_positive source r hr))
  dsimp only [width,natBitLength]
  rw [pow_succ]
  omega

end NearCubicWires.RepairSource.ProjectionNormalization.Dimensions
