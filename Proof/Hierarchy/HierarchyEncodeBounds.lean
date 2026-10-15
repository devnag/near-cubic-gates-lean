import Proof.Hierarchy.HierarchyEncode

/-! Fixed-slice coefficient transport keeps the padding coefficient and
hierarchy coefficient separate. In particular the padded length is only
bounded by a fixed multiple of the original hierarchy clock. -/
namespace NearCubicWires.RepairSource.HierarchyEncode
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def lengthCoefficient {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) :=
  2*Cpad+1+HierarchyBinary.header (VerifierEncoding.code H.verifier).length H.coefficient+2^(k+2)
def capCoefficient {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) :=
  2^(k+2)*((2*lengthCoefficient H Cpad)^(k+2)*Cpad)
def massCoefficient {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) :=
  lengthCoefficient H Cpad+capCoefficient H Cpad+1
def qCoefficient {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) :=
  logScale (lengthCoefficient H Cpad)+2
def timeCoefficient {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) :=
  268435456*massCoefficient H Cpad*(qCoefficient H Cpad)^5
def timeLogCoefficient {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) :=
  logScale (timeCoefficient H Cpad)+6

theorem hierarchy_input_bound {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (n : ℕ) :
    n+1 ≤ H.time n := by
  have hp : n ≤ n^(k+2) := Nat.le_self_pow (by omega) n
  have hc := Nat.mul_le_mul_right (n^(k+2)+1) (show 1 ≤ H.coefficient by have := H.coefficientPositive; omega)
  change n+1 ≤ H.coefficient*(n^(k+2)+1)
  omega

theorem length_bound {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad n : ℕ) :
    length H Cpad n ≤ lengthCoefficient H Cpad*H.time n := by
  have hl := (PowerSlice.linear_length k (2*Cpad)
    (HierarchyBinary.header (VerifierEncoding.code H.verifier).length H.coefficient) n).2
  exact hl.trans (Nat.mul_le_mul_left _ (hierarchy_input_bound H n))

theorem cap_bound {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (n : ℕ) :
    ClockDyadicLedger.limit (length H Cpad n) ≤ capCoefficient H Cpad*H.time n := by
  have hp := (PCPResourceLedger.separate_padding k H.coefficient Cpad
    (HierarchyBinary.header (VerifierEncoding.code H.verifier).length H.coefficient) n
    (by have := H.coefficientPositive; omega) hcoeff).2
  have hs := (ClockDyadicLedger.fixed_slice k
    (HierarchyBinary.allocation Cpad (VerifierEncoding.code H.verifier).length H.coefficient n)).2
  calc _ ≤ 2^(k+2)*PowerSlice.limit (length H Cpad n) := hs
       _ ≤ 2^(k+2)*(((2*lengthCoefficient H Cpad)^(k+2)*Cpad)*H.time n) :=
         Nat.mul_le_mul_left _ hp
       _ = capCoefficient H Cpad*H.time n := by simp only [capCoefficient]; ring

theorem mass_bound {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (n : ℕ) :
    length H Cpad n+ClockDyadicLedger.limit (length H Cpad n)+1 ≤ massCoefficient H Cpad*H.time n := by
  have hl := length_bound H Cpad n
  have hc := cap_bound H Cpad hcoeff n
  have hb := hierarchy_input_bound H n
  dsimp only [massCoefficient]
  nlinarith

theorem logScale_monomial_bound (A B d N : ℕ) (hN : N ≤ A*B*(logScale B)^d) :
    logScale N ≤ (logScale A+d+1)*logScale B := by
  have hA : A+2 ≤ 2^logScale A := Nat.le_pow_clog (by decide) _
  have hB : B+2 ≤ 2^logScale B := Nat.le_pow_clog (by decide) _
  have hlog : 1 ≤ logScale B := Nat.clog_pos (by decide) (by omega)
  have hlogpow : logScale B ≤ 2^logScale B := (Nat.lt_two_pow_self).le
  have hfactor : 1 ≤ (2^logScale B)^d := Nat.one_le_pow _ _ (by positivity)
  have hsmall : N+2 ≤ (A+2)*(B+2)*(2^logScale B)^d := by
    have hm := hN.trans (Nat.mul_le_mul_left (A*B) (Nat.pow_le_pow_left hlogpow d))
    nlinarith
  have hpower : N+2 ≤ 2^(logScale A+(d+1)*logScale B) := by
    calc _ ≤ (A+2)*(B+2)*(2^logScale B)^d := hsmall
         _ ≤ (2^logScale A)*(2^logScale B)*(2^logScale B)^d := by gcongr
         _ = 2^(logScale A+(d+1)*logScale B) := by
           rw [←pow_mul,←pow_add,←pow_add]
           congr 1
           ring
  have hc : logScale N ≤ logScale A+(d+1)*logScale B := Nat.clog_le_of_le_pow hpower
  have hm := Nat.mul_le_mul_left (logScale A) hlog
  nlinarith

theorem q_bound {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad n : ℕ) :
    PCPResourceLedger.q (length H Cpad n) ≤ qCoefficient H Cpad*logScale (H.time n) := by
  have hlog := logScale_monomial_bound (lengthCoefficient H Cpad) (H.time n) 0
    (length H Cpad n) (by simpa using length_bound H Cpad n)
  have he : PCPResourceLedger.ell (length H Cpad n) ≤ logScale (length H Cpad n) :=
    Nat.clog_mono_right 2 (by omega)
  have hb : 1 ≤ logScale (H.time n) := Nat.clog_pos (by decide) (by omega)
  dsimp only [qCoefficient,PCPResourceLedger.q]
  nlinarith

theorem time_bound {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (n : ℕ) :
    UAggregateClock.time (length H Cpad n) ≤ timeCoefficient H Cpad*H.time n*logScale (H.time n)^5 := by
  have hu := (UAggregateClock.time_bounds (length H Cpad n)).2
  calc _ ≤ 268435456*(length H Cpad n+ClockDyadicLedger.limit (length H Cpad n)+1)*
      PCPResourceLedger.q (length H Cpad n)^5 := hu
       _ ≤ 268435456*(massCoefficient H Cpad*H.time n)*(qCoefficient H Cpad*logScale (H.time n))^5 :=
         Nat.mul_le_mul (Nat.mul_le_mul_left _ (mass_bound H Cpad hcoeff n))
           (Nat.pow_le_pow_left (q_bound H Cpad n) 5)
       _ = timeCoefficient H Cpad*H.time n*logScale (H.time n)^5 := by
         simp only [timeCoefficient,mul_pow]
         ring

theorem time_log_bound {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (n : ℕ) :
    logScale (UAggregateClock.time (length H Cpad n)) ≤ timeLogCoefficient H Cpad*logScale (H.time n) :=
  logScale_monomial_bound (timeCoefficient H Cpad) (H.time n) 5 _ (time_bound H Cpad hcoeff n)

end NearCubicWires.RepairSource.HierarchyEncode
