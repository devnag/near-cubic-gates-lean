import Proof.MachineModel.ClockBinary

/-! Dyadic implementation of the fixed-U cap. A fixed hierarchy slice changes
only its constant factor. Width construction requires unary multiplication
of logarithmic counts, rather than exponentiation of binary scalar values. -/
namespace NearCubicWires.RepairOrdinary.ClockDyadicLedger
open PCPResourceLedger
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def exponent (N : ℕ) : ℕ := PowerSlice.degree N*ell N
def limit (N : ℕ) : ℕ := 2^exponent N
def width (N : ℕ) : ℕ := exponent N+3

theorem bit_width (N : ℕ) : (ClockBinary.word N).length = ell N := by
  by_cases hz : N=0
  · simp [hz,ClockBinary.word,ell]
  have hp : 0<N := Nat.pos_of_ne_zero hz
  rw [ClockBinary.length_log N hp]
  apply Nat.le_antisymm
  · have hN := Nat.le_pow_clog (by decide : 1<2) (N+1)
    have := Nat.log_lt_of_lt_pow hz (lt_of_lt_of_le (Nat.lt_succ_self N) hN)
    dsimp only [ell]
    omega
  · apply Nat.clog_le_of_le_pow
    exact Nat.succ_le_of_lt (Nat.lt_pow_succ_log_self (by decide : 1<2) N)

theorem pow_ell_bounds (N : ℕ) (hN : 1≤N) : N<2^ell N ∧ 2^ell N≤2*N := by
  refine ⟨lt_of_lt_of_le (Nat.lt_succ_self N) (Nat.le_pow_clog (by decide) _),?_⟩
  rw [← bit_width, ClockBinary.length_log N (by omega), pow_succ]
  have hp := Nat.pow_log_le_self 2 (by omega : N≠0)
  omega

theorem limit_bounds (N : ℕ) (hN : 1≤N) :
    PowerSlice.limit N ≤ limit N ∧ limit N ≤ 2^PowerSlice.degree N*PowerSlice.limit N := by
  have hb := pow_ell_bounds N hN
  have he : limit N = (2^ell N)^PowerSlice.degree N := by
    simp only [limit,exponent,← pow_mul]
    rw [Nat.mul_comm]
  rw [he]
  constructor
  · exact Nat.pow_le_pow_left hb.1.le _
  · simpa [mul_pow,PowerSlice.limit] using Nat.pow_le_pow_left hb.2 (PowerSlice.degree N)

theorem width_bounds (N : ℕ) : 4*limit N+4 ≤ 2^width N ∧ width N≤3*q N^2 := by
  have hlimit : 1≤limit N := Nat.one_le_pow _ _ (by decide)
  have hN : N≤2^ell N := (Nat.le_succ N).trans (Nat.le_pow_clog (by decide) _)
  have hD : PowerSlice.degree N≤ell N+2 := by
    have := Nat.factorization_le_of_le_pow hN
    dsimp only [PowerSlice.degree]
    omega
  constructor
  · rw [width,pow_add]
    change 4*limit N+4 ≤ limit N*8
    omega
  · dsimp only [width,exponent,q]
    have := Nat.mul_le_mul_right (ell N) hD
    nlinarith

theorem guarded_bounds (N n B m t c : ℕ) (hN : 2≤N)
    (hn : n≤B) (hB : B≤limit N) (hm : m≤B) (ht : t≤c) (hc : c≤Nat.log 2 N) :
    events n B m t < 2^(2*width N) ∧
    N+events n B m t+1 ≤ 7*limit N*q N ∧
    width N+c+1 ≤ 4*q N^2 ∧
    width N+B+t*m ≤ 4*limit N*q N^2 := by
  have hNL : N≤limit N := (Nat.le_self_pow (by simp [PowerSlice.degree]) N).trans
    (limit_bounds N (by omega)).1
  have hL : 2≤limit N := hN.trans hNL
  have hce : c≤ell N := hc.trans
    ((Nat.log_mono_right (Nat.le_succ N)).trans (Nat.log_le_clog 2 (N+1)))
  have heN : ell N≤N := by
    apply Nat.clog_le_of_le_pow
    exact Nat.succ_le_of_lt Nat.lt_two_pow_self
  have hcap := record_capacity n B m t c (limit N) (width N) hL hn hB hm ht
    (hce.trans (heN.trans hNL)) (width_bounds N).1
  have hcurrency := reduced_currency N n B m t c (limit N) (width N) (q N)
    hL hNL hn hB hm ht (by simp [q]) (by dsimp [q]; omega) (width_bounds N).2
  exact ⟨hcap.1,hcurrency⟩

def clock (C d N : ℕ) : ℕ := C*(N+limit N+1)*q N^(2*d+1)

theorem clock_covers (A C d N X z witnessBits : ℕ) (hC : 4≤C) (hd : 1≤d)
    (hA : 7*A*4^d≤C) (hX : X≤7*limit N*q N)
    (hz : z≤4*q N^2) (hp : witnessBits≤4*limit N*q N^2) :
    N≤clock C d N ∧ witnessBits≤clock C d N ∧ A*X*z^d≤clock C d N := by
  have hq : 1≤q N := by simp [q]
  have hqpow : 1≤q N^(2*d+1) := Nat.one_le_pow _ _ hq
  have hcoeff : limit N≤N+limit N+1 := by omega
  have hprecoeff : 4*limit N≤C*(N+limit N+1) := Nat.mul_le_mul hC hcoeff
  have hprecost := Nat.mul_le_mul hprecoeff
    (Nat.pow_le_pow_right hq (by omega : 2≤2*d+1))
  have hwhole := (aggregate A (limit N) (q N) X z d hX hz).trans
    (Nat.mul_le_mul_right (q N^(2*d+1)) (Nat.mul_le_mul hA hcoeff))
  refine ⟨?_,hp.trans hprecost,hwhole⟩
  have hbase : N≤C*(N+limit N+1) := by nlinarith
  have hmul := Nat.mul_le_mul_left (C*(N+limit N+1)) hqpow
  exact hbase.trans (by simpa only [mul_one,clock] using hmul)

theorem fixed_slice (k a : ℕ) :
    PowerSlice.limit (PowerSlice.length k a) ≤ limit (PowerSlice.length k a) ∧
    limit (PowerSlice.length k a) ≤ 2^(k+2)*PowerSlice.limit (PowerSlice.length k a) := by
  have hN : 1≤PowerSlice.length k a := by
    have := (PowerSlice.length_bounds k a).1
    omega
  have h := limit_bounds (PowerSlice.length k a) hN
  simpa [PowerSlice.length_degree] using h

end NearCubicWires.RepairOrdinary.ClockDyadicLedger
