import Proof.CaseAnalysis.RowsRawOccurrenceBound

/-! Finite arithmetic test of the actual raw-list logarithmic recurrence.
W is the sum of graded windows, h their count, ell the native logarithmic
population bound, and a the child-population bit bound. This is a shape
lemma, not the missing source-specific recurrence/onset application. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawLogShape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def baseLog (W h ell : ℕ) := 5+h*ell+6*(W+h)*(ell+2)+2*W
def coordinateLog (t W h ell : ℕ) := (t+1)+(t*(baseLog W h ell+1)+1)
def rowWidth (z t W h ell a : ℕ) := z*(ell+coordinateLog t W h ell)+2*z*t*W*a+6

theorem row_bound (z t W h ell a : ℕ) (ha : a ≤ ell) :
    rowWidth z t W h ell a ≤ 128*(z+1)*(t+1)*(W+h+1)*(ell+1) := by
  have hm:=Nat.mul_le_mul_left (2*z*t*W) ha
  have he : rowWidth z t W h ell ell ≤ 128*(z+1)*(t+1)*(W+h+1)*(ell+1) := by
    unfold rowWidth coordinateLog baseLog
    ring_nf
    omega
  exact (show rowWidth z t W h ell a ≤ rowWidth z t W h ell ell by
    unfold rowWidth
    omega).trans he

theorem digit_load (K z t W h ell a : ℕ) (ha : a ≤ ell) :
    K+rowWidth z t W h ell a*(K+2) ≤
      K+128*(z+1)*(t+1)*(W+h+1)*(ell+1)*(K+2) := by
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (row_bound z t W h ell a ha)) _

theorem symmetric_power : 4+2*0+2*0=5-1 := by decide
theorem threshold_power : 4+2*1+2*1=9-1 := by decide

end NearCubicWires.RepairOrdinary.CloseoutRowsRawLogShape
