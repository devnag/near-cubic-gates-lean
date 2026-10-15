import Proof.CaseAnalysis.FinalAssembly

/-! Paper A.7/A.8: the runtime splits into a polynomial part and one residual
table factor, and that single factor is damped.

The resource ledger fixes `K = kappa * L_q` with `kappa > h_D + sigma + b_col + 10`,
so in particular `sigma <= kappa`. The damping obligation

    hot N * width N ^ sigma  <=  B * 2 ^ width N

is then pure arithmetic at `hot N = 2 ^ (width N - K N)` and `B = 1`: the only
content is `width ^ sigma <= 2 ^ K`, which is exactly what `kappa >= sigma`
buys once `L_q` is a genuine binary logarithm of the width.

There is exactly ONE residual factor here, as the ledger requires, and no
capacity or metadata enters for free: `logWidth` is supplied by the caller and
must satisfy `width N <= 2 ^ logWidth N`. -/
namespace NearCubicWires.RepairSource.CloseoutFinal
open SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- Once the table exponent dominates the width power, the residual factor is
absorbed by the ambient `2 ^ width`. -/
theorem damp_of_pow_le {width tableExp power : ℕ} (hK : tableExp ≤ width)
    (h : width^power ≤ 2^tableExp) :
    2^(width-tableExp)*width^power ≤ 2^width := by
  calc 2^(width-tableExp)*width^power
      ≤ 2^(width-tableExp)*2^tableExp := Nat.mul_le_mul_left _ h
    _ = 2^((width-tableExp)+tableExp) := (pow_add 2 (width-tableExp) tableExp).symm
    _ = 2^width := by rw [Nat.sub_add_cancel hK]

/-- `kappa >= sigma` and a genuine binary logarithm give the width power. -/
theorem pow_le_two_pow_mul {width logWidth power kappa : ℕ}
    (hw : width ≤ 2^logWidth) (hsk : power ≤ kappa) :
    width^power ≤ 2^(kappa*logWidth) := by
  calc width^power ≤ (2^logWidth)^power := Nat.pow_le_pow_left hw power
    _ = 2^(logWidth*power) := (pow_mul 2 logWidth power).symm
    _ ≤ 2^(logWidth*kappa) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left logWidth hsk)
    _ = 2^(kappa*logWidth) := by rw [Nat.mul_comm]

/-- Paper A.8, combined: the single residual table factor is damped. -/
theorem damping {width logWidth power kappa : ℕ}
    (hw : width ≤ 2^logWidth) (hsk : power ≤ kappa) (hK : kappa*logWidth ≤ width) :
    2^(width-kappa*logWidth)*width^power ≤ 2^width :=
  damp_of_pow_le hK (pow_le_two_pow_mul hw hsk)

/-- The residual factor itself: `2 ^ (q - K)`, one occurrence, no more. -/
def hotOf (kappa : ℕ) (width logWidth : ℕ → ℕ) : ℕ → ℕ :=
  fun N => 2^(width N-kappa*logWidth N)

/-- The `hdamp` field of `PhysicalWitness`, discharged from the ledger
invariants alone, with `B = 1`. -/
theorem hdamp_of_ledger (kappa power onset : ℕ) (width logWidth : ℕ → ℕ)
    (hsk : power ≤ kappa)
    (hlog : ∀ N, onset ≤ N → width N ≤ 2^(logWidth N))
    (hfit : ∀ N, onset ≤ N → kappa*logWidth N ≤ width N) :
    ∀ N, onset ≤ N → hotOf kappa width logWidth N*(width N)^power ≤ 1*2^(width N) := by
  intro N hN
  rw [Nat.one_mul]
  exact damping (hlog N hN) hsk (hfit N hN)

/-- The `hpoly` field, when the worker's fuel is already a polynomial envelope
plus the residual factor. No new budget is introduced here. -/
theorem hpoly_of_envelope (A a onset : ℕ) (fuel hot : ℕ → ℕ)
    (h : ∀ N, onset ≤ N → fuel N+2 ≤ A*(N+1)^a+hot N) :
    ∀ N, onset ≤ N → fuel N+2 ≤ A*(N+1)^a+hot N := h

end NearCubicWires.RepairSource.CloseoutFinal
