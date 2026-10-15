import Proof.Hierarchy.HierarchySelectedSource

/-! Scalar transport to the original hierarchy input and its short clock.
All hierarchy dependence stays in coefficients; source exponents are fixed. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchySourceScales
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bits_length_le (n : ℕ) : n.bits.length ≤ natBitLength n := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  exact Nat.lt_pow_succ_log_self (by decide) n

theorem logScale_le_short (n : ℕ) : logScale n ≤ natBitLength n+1 := by
  have hn := Nat.lt_pow_succ_log_self (b:=2) (by decide) n
  have hp : 1 ≤ 2^(Nat.log 2 n+1) := Nat.one_le_pow _ _ (by decide)
  apply Nat.clog_le_of_le_pow
  change n+2 ≤ 2^(Nat.log 2 n+1+1)
  rw [pow_succ]
  omega

theorem short_le_logScale (n : ℕ) : natBitLength n+1 ≤ logScale n+2 := by
  have h := (Nat.log_le_clog 2 n).trans (Nat.clog_mono_right 2 (show n ≤ n+2 by omega))
  change Nat.log 2 n+1+1 ≤ Nat.clog 2 (n+2)+2
  omega

def Ncoefficient {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) :=
  HierarchyEncode.lengthCoefficient H Cpad+1
def Tcoefficient {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) :=
  HierarchyEncode.timeLogCoefficient H Cpad+2

theorem length_bound {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad n : ℕ) :
    HierarchyEncode.length H Cpad n+1 ≤ Ncoefficient H Cpad*(n+1) := by
  have h := (PowerSlice.linear_length k (2*Cpad)
    (HierarchyBinary.header (VerifierEncoding.code H.verifier).length H.coefficient) n).2
  change HierarchyEncode.length H Cpad n ≤ HierarchyEncode.lengthCoefficient H Cpad*(n+1) at h
  dsimp [Ncoefficient]
  nlinarith

theorem input_q_bound {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (n : ℕ) :
    PCPResourceLedger.q n ≤ 2*(natBitLength (H.time n)+1) := by
  have hn := HierarchyEncode.hierarchy_input_bound H n
  have he : PCPResourceLedger.ell n ≤ logScale (H.time n) := Nat.clog_mono_right 2 (by omega)
  have hl := logScale_le_short (H.time n)
  dsimp [PCPResourceLedger.q]
  omega

theorem padded_q_bound {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad n : ℕ) :
    PCPResourceLedger.q (HierarchyEncode.length H Cpad n) ≤
      HierarchyEncode.qCoefficient H Cpad*(natBitLength (H.time n)+1) :=
  (HierarchyEncode.q_bound H Cpad n).trans
    (Nat.mul_le_mul_left _ (logScale_le_short (H.time n)))

theorem time_short_bound {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (n : ℕ) :
    natBitLength (UWhole.time (HierarchyEncode.length H Cpad n))+1 ≤
      Tcoefficient H Cpad*(natBitLength (H.time n)+1) := by
  have hu := short_le_logScale (UWhole.time (HierarchyEncode.length H Cpad n))
  have ht := HierarchyEncode.time_log_bound H Cpad hcoeff n
  have hl := logScale_le_short (H.time n)
  have hp : 1 ≤ natBitLength (H.time n)+1 := by omega
  have hm := Nat.mul_le_mul_left (HierarchyEncode.timeLogCoefficient H Cpad) hl
  dsimp only [Tcoefficient]
  change logScale (UWhole.time (HierarchyEncode.length H Cpad n)) ≤
    HierarchyEncode.timeLogCoefficient H Cpad*logScale (H.time n) at ht
  nlinarith

theorem monomial_le (X Z a b i j : ℕ) (hX : 1 ≤ X) (hZ : 1 ≤ Z)
    (hi : i ≤ a) (hj : j ≤ b) : X^i*Z^j ≤ X^a*Z^b :=
  Nat.mul_le_mul (Nat.pow_le_pow_right hX hi) (Nat.pow_le_pow_right hZ hj)

end NearCubicWires.RepairSource.ProjectionNormalization.HierarchySourceScales
