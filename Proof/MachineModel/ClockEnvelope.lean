import Proof.MachineModel.ClockUniversalBound

/-! A dyadic global U clock changes the accepted near-linear clock by only
a fixed multiplicative constant. All new exponents are fixed with U. -/
namespace NearCubicWires.RepairOrdinary.ClockEnvelope
open PCPResourceLedger
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def logWidth (N : ℕ) : ℕ := ell (ell N)
def exponent (k c N : ℕ) : ℕ := ClockDyadicLedger.exponent N+c*logWidth N+k
def clock (k c N : ℕ) : ℕ := 2^exponent k c N
def original (C c N : ℕ) : ℕ := C*(N+ClockDyadicLedger.limit N+1)*q N^c

theorem logWidth_eq (N : ℕ) : logWidth N=(ClockBinary.word (ell N)).length :=
  (ClockDyadicLedger.bit_width (ell N)).symm
theorem logWidth_bounds (N : ℕ) : q N≤2^logWidth N ∧ 2^logWidth N≤2*q N := by
  constructor
  · exact Nat.le_pow_clog (by decide) (ell N+1)
  · by_cases hz : ell N=0
    · simp only [logWidth,q,hz]; decide
    · have hb := (ClockDyadicLedger.pow_ell_bounds (ell N) (by omega)).2
      dsimp only [logWidth,q]
      omega

theorem input_le_limit (N : ℕ) : N≤ClockDyadicLedger.limit N := by
  by_cases hz : N=0
  · simp [hz]
  · exact (Nat.le_self_pow (by simp [PowerSlice.degree]) N).trans
      (ClockDyadicLedger.limit_bounds N (by omega)).1

theorem clock_factor (k c N : ℕ) :
    clock k c N=2^k*ClockDyadicLedger.limit N*(2^logWidth N)^c := by
  simp only [clock,exponent,ClockDyadicLedger.limit,pow_add]
  rw [Nat.mul_comm c (logWidth N),pow_mul]
  ring

theorem envelope (C k c N : ℕ) (hC : 3*C≤2^k) :
    original C c N≤clock k c N ∧
      clock k c N≤2^(k+c)*(N+ClockDyadicLedger.limit N+1)*q N^c := by
  have hN := input_le_limit N
  have hL : 1≤ClockDyadicLedger.limit N := Nat.one_le_pow _ _ (by decide)
  have hq := logWidth_bounds N
  constructor
  · have hcoeff : C*(N+ClockDyadicLedger.limit N+1)≤2^k*ClockDyadicLedger.limit N :=
      calc C*(N+ClockDyadicLedger.limit N+1)≤(3*C)*ClockDyadicLedger.limit N := by nlinarith
           _≤2^k*ClockDyadicLedger.limit N := Nat.mul_le_mul_right _ hC
    have h := Nat.mul_le_mul hcoeff (Nat.pow_le_pow_left hq.1 c)
    simpa only [original,clock_factor] using h
  · calc clock k c N≤2^k*ClockDyadicLedger.limit N*(2*q N)^c := by
          rw [clock_factor]
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hq.2 c)
        _=2^(k+c)*ClockDyadicLedger.limit N*q N^c := by rw [mul_pow,pow_add]; ring
        _≤2^(k+c)*(N+ClockDyadicLedger.limit N+1)*q N^c :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))

theorem constant_factor (C k c N : ℕ) (hC : 1≤C) (hk : 3*C≤2^k) :
    original C c N≤clock k c N ∧ clock k c N≤2^(k+c)*original C c N := by
  have h := envelope C k c N hk
  refine ⟨h.1,h.2.trans ?_⟩
  have hbase : (N+ClockDyadicLedger.limit N+1)*q N^c≤original C c N := by
    dsimp only [original]
    have h' := Nat.mul_le_mul_right ((N+ClockDyadicLedger.limit N+1)*q N^c) hC
    simpa only [one_mul,Nat.mul_assoc] using h'
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (2^(k+c)) hbase

theorem exponent_bound (k c N : ℕ) : exponent k c N+3≤(c+k+4)*q N^2 := by
  have hw := (ClockDyadicLedger.width_bounds N).2
  have hh : logWidth N≤ell N := Nat.clog_le_of_le_pow (Nat.succ_le_of_lt Nat.lt_two_pow_self)
  have hq : 1≤q N := by simp [q]
  have he : ell N≤q N := by simp [q]
  have hq2 : q N≤q N^2 := by nlinarith
  have hch : c*logWidth N≤c*(q N^2) := Nat.mul_le_mul_left _ (hh.trans (he.trans hq2))
  have hk : k≤k*q N^2 := by nlinarith
  dsimp only [exponent,ClockDyadicLedger.width] at *
  nlinarith

theorem covers (A C d k N X z witnessBits : ℕ) (hC : 4≤C) (hd : 1≤d)
    (hA : 7*A*4^d≤C) (hk : 3*C≤2^k) (hX : X≤7*ClockDyadicLedger.limit N*q N)
    (hz : z≤4*q N^2) (hp : witnessBits≤4*ClockDyadicLedger.limit N*q N^2) :
    N≤clock k (2*d+1) N ∧ witnessBits≤clock k (2*d+1) N ∧ A*X*z^d≤clock k (2*d+1) N := by
  have hc := ClockDyadicLedger.clock_covers A C d N X z witnessBits hC hd hA hX hz hp
  have he := (envelope C k (2*d+1) N hk).1
  exact ⟨hc.1.trans he,hc.2.1.trans he,hc.2.2.trans he⟩

end NearCubicWires.RepairOrdinary.ClockEnvelope
