import Proof.PCP.ProjectionPCPTransport
import Mathlib.Data.Nat.Factorization.Basic

/-! Exact length slices for the one fixed computation-log verifier.
The slice index k selects hierarchy degree k+2. These are mathematical
length/clock identities; padding and binary clock computation still need
their ordinary execution receipts. Factorization denotes the 2-adic order,
not a proposed implementation by general integer factorization. -/
namespace NearCubicWires.RepairOrdinary.PowerSlice
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def degree (N : ℕ) : ℕ := 2 + N.factorization 2
def limit (N : ℕ) : ℕ := N ^ degree N
def length (k A : ℕ) : ℕ := 2^(k+1) * (A / 2^(k+1) + 1) + 2^k

theorem length_form (k A : ℕ) :
    length k A = 2^k * (2*(A / 2^(k+1) + 1) + 1) := by
  simp only [length, pow_succ]
  ring

theorem length_bounds (k A : ℕ) : A < length k A ∧ length k A ≤ A + 2^(k+2) := by
  have hp : 0 < 2^(k+1) := by positivity
  have hr := Nat.mod_lt A hp
  have he := Nat.mod_add_div A (2^(k+1))
  have hd := Nat.mul_div_le A (2^(k+1))
  have hk : 0 < 2^k := by positivity
  dsimp only [length]
  rw [Nat.mul_add, Nat.mul_one]
  have hpow : 2^(k+2) = 2^(k+1) + 2^(k+1) := by
    rw [show k+2 = (k+1)+1 by omega, pow_succ]
    omega
  have hsmall : 2^k ≤ 2^(k+1) := Nat.pow_le_pow_right (by omega) (by omega)
  constructor <;> omega

theorem length_degree (k A : ℕ) : degree (length k A) = k+2 := by
  have hodd : ¬2 ∣ 2*(A / 2^(k+1) + 1)+1 := by omega
  have hn : 2*(A / 2^(k+1) + 1)+1 ≠ 0 := by omega
  rw [degree, length_form, Nat.factorization_mul (by positivity) hn]
  simp only [Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hodd]
  omega

theorem length_limit (k A : ℕ) : limit (length k A) = length k A ^ (k+2) := by
  rw [limit, length_degree]

/-- A fixed hierarchy's framed header fits by a fixed linear coefficient.
The slice remains linearly bounded in n, with constants allowed to depend
on that hierarchy and its already selected power-clock degree. -/
theorem linear_length (k coefficient header n : ℕ) :
    n+1 ≤ length k ((coefficient+1)*(n+1)+header) ∧
      length k ((coefficient+1)*(n+1)+header) ≤
        (coefficient+1+header+2^(k+2))*(n+1) := by
  obtain ⟨hl, hu⟩ := length_bounds k ((coefficient+1)*(n+1)+header)
  have hc : n+1 ≤ (coefficient+1)*(n+1) := by nlinarith
  constructor
  · omega
  · nlinarith

/-- The source hierarchy uses B=C*(n^(k+2)+1), not an arbitrary clock with
only a polynomial upper bound. Padding with coefficient at least 2*C
puts the entire bounded computation inside the selected verifier slice. -/
theorem hierarchy_fits (k C header n : ℕ) :
    C*(n^(k+2)+1) ≤ limit (length k ((2*C+1)*(n+1)+header)) := by
  let N := length k ((2*C+1)*(n+1)+header)
  have hN : (2*C+1)*(n+1) ≤ N := by
    have := (length_bounds k ((2*C+1)*(n+1)+header)).1
    dsimp only [N]
    omega
  have hbase : n^(k+2)+1 ≤ 2*(n+1)^(k+2) := by
    have hn := Nat.pow_le_pow_left (show n ≤ n+1 by omega) (k+2)
    have hp : 1 ≤ (n+1)^(k+2) := Nat.one_le_pow _ _ (by omega)
    omega
  have hcoef : 2*C ≤ (2*C+1)^(k+2) := by
    have hp := Nat.le_self_pow (by omega : k+2 ≠ 0) (2*C+1)
    omega
  rw [length_limit]
  calc
    C*(n^(k+2)+1) ≤ C*(2*(n+1)^(k+2)) := Nat.mul_le_mul_left _ hbase
    _ = (2*C)*(n+1)^(k+2) := by ring
    _ ≤ (2*C+1)^(k+2)*(n+1)^(k+2) := Nat.mul_le_mul_right _ hcoef
    _ = ((2*C+1)*(n+1))^(k+2) := (Nat.mul_pow _ _ _).symm
    _ ≤ N^(k+2) := Nat.pow_le_pow_left hN _

/-- On the selected slice the verifier limit is only a hierarchy-dependent
constant times the original hierarchy clock. This reverse comparison is
essential; merely proving that the hierarchy fits would not suffice. -/
theorem hierarchy_limit_bound (k C header n : ℕ) (hC : 0 < C) :
    limit (length k ((2*C+1)*(n+1)+header)) ≤
      (2*(2*C+1+header+2^(k+2)))^(k+2) * (C*(n^(k+2)+1)) := by
  let a := 2*C+1+header+2^(k+2)
  have hlen := (linear_length k (2*C) header n).2
  have hp : (n+1)^(k+2) ≤ 2^(k+2)*(n^(k+2)+1) := by
    cases n with
    | zero => simp only [zero_add, one_pow, zero_pow (by omega : k+2 ≠ 0), mul_one]
              exact Nat.one_le_pow _ _ (by omega)
    | succ n =>
      calc
        (n+1+1)^(k+2) ≤ (2*(n+1))^(k+2) := Nat.pow_le_pow_left (by omega) _
        _ = 2^(k+2)*(n+1)^(k+2) := Nat.mul_pow _ _ _
        _ ≤ 2^(k+2)*((n+1)^(k+2)+1) := Nat.mul_le_mul_left _ (by omega)
  rw [length_limit]
  calc
    length k ((2*C+1)*(n+1)+header)^(k+2) ≤ (a*(n+1))^(k+2) :=
      Nat.pow_le_pow_left hlen _
    _ = a^(k+2)*(n+1)^(k+2) := Nat.mul_pow _ _ _
    _ ≤ a^(k+2)*(2^(k+2)*(n^(k+2)+1)) := Nat.mul_le_mul_left _ hp
    _ = (2*a)^(k+2)*(n^(k+2)+1) := by rw [Nat.mul_pow]; ring
    _ ≤ (2*a)^(k+2)*(C*(n^(k+2)+1)) :=
      Nat.mul_le_mul_left _ (by
        simpa only [one_mul] using Nat.mul_le_mul_right (n^(k+2)+1) (show 1 ≤ C by omega))

end NearCubicWires.RepairOrdinary.PowerSlice
