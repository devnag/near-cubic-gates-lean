import SourceAdapters.Code.Parsing

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": polynomial bookkeeping for paid ordinary cell compilation.
The judgement concerns numerical runtime bounds, not machine existence. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.PolynomialCosts

open NearCubicGates.Close.Cells

variable {R : Type} (measure : R → ℕ)

def Bound (f : R → ℕ) : Prop := ∃ K e : ℕ, ∀ r, f r ≤ K * (measure r + 1) ^ e

variable {measure}

theorem constant (K : ℕ) : Bound measure (fun _ => K) := ⟨K, 0, fun _ => by simp⟩

theorem self : Bound measure measure := ⟨1, 1, fun _ => by simp⟩

theorem mono {f g : R → ℕ} (h : Bound measure g) (hle : ∀ r, f r ≤ g r) : Bound measure f := by
  obtain ⟨K, e, h⟩ := h
  exact ⟨K, e, fun r => (hle r).trans (h r)⟩

theorem add {f g : R → ℕ} (hf : Bound measure f) (hg : Bound measure g) :
    Bound measure (fun r => f r + g r) := by
  obtain ⟨K, e, hf⟩ := hf
  obtain ⟨A, d, hg⟩ := hg
  refine ⟨K + A, e + d, fun r => ?_⟩
  have he := Nat.pow_le_pow_right (show 1 ≤ measure r + 1 by omega) (show e ≤ e + d by omega)
  have hd := Nat.pow_le_pow_right (show 1 ≤ measure r + 1 by omega) (show d ≤ e + d by omega)
  have h1 := (hf r).trans (Nat.mul_le_mul_left K he)
  have h2 := (hg r).trans (Nat.mul_le_mul_left A hd)
  calc f r + g r ≤ K * (measure r + 1) ^ (e + d) + A * (measure r + 1) ^ (e + d) := Nat.add_le_add h1 h2
    _ = _ := by ring

theorem mul {f g : R → ℕ} (hf : Bound measure f) (hg : Bound measure g) :
    Bound measure (fun r => f r * g r) := by
  obtain ⟨K, e, hf⟩ := hf
  obtain ⟨A, d, hg⟩ := hg
  refine ⟨K * A, e + d, fun r => ?_⟩
  calc f r * g r ≤ (K * (measure r + 1) ^ e) * (A * (measure r + 1) ^ d) := Nat.mul_le_mul (hf r) (hg r)
    _ = _ := by rw [pow_add]; ring

theorem pow {f : R → ℕ} (hf : Bound measure f) (d : ℕ) : Bound measure (fun r => f r ^ d) := by
  obtain ⟨K, e, hf⟩ := hf
  refine ⟨K ^ d, e * d, fun r => ?_⟩
  calc f r ^ d ≤ (K * (measure r + 1) ^ e) ^ d := Nat.pow_le_pow_left (hf r) d
    _ = _ := by rw [mul_pow, ← pow_mul]

theorem language (K : Callee) (z : Sz) (V M : ℕ) (input : R → List Bool) (N : R → ℕ)
    (hL : Bound measure (fun r => leadOnes (input r)))
    (hW : Bound measure (fun r => z.W (leadOnes (input r))))
    (hI : Bound measure (fun r => z.Lk (leadOnes (input r))))
    (hB : Bound measure (fun r => z.Bk (leadOnes (input r))))
    (hword : Bound measure (fun r => (input r).length)) (hN : Bound measure N) :
    Bound measure (fun r => langBudget K z V M (input r) (N r)) := by
  dsimp only [langBudget, costA, costB, costC]
  repeat' first
    | exact hL
    | exact hW
    | exact hI
    | exact hB
    | exact hword
    | exact hN
    | exact constant _
    | apply add
    | apply mul

end NearCubicGates.Adapters.Code.PolynomialCosts
