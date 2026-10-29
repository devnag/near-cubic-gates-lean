import SourceAdapters.Proximity.NumericalConstructor

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": uniform polynomial domination of numerical
resource families. The addition/multiplication proofs use the scalar budget
inequalities of ValidatorPolynomialDomination, now quantified over requests. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Growth

variable {α : Type} (size : α → ℕ)

def Bounded (value : α → ℕ) : Prop := ∃ K e : ℕ, ∀ x, value x ≤ K * (size x + 1) ^ e

variable {size}

theorem Bounded.mono {f g : α → ℕ} (h : Bounded size f) (hle : ∀ x, g x ≤ f x) : Bounded size g := by
  obtain ⟨K, e, hK⟩ := h
  exact ⟨K, e, fun x => (hle x).trans (hK x)⟩

theorem bounded_const (c : ℕ) : Bounded size (fun _ : α => c) := ⟨c, 0, fun _ => by simp⟩

theorem bounded_size : Bounded size size := ⟨1, 1, fun _ => by simp⟩

theorem Bounded.add {f g : α → ℕ} (hf : Bounded size f) (hg : Bounded size g) :
    Bounded size (fun x => f x + g x) := by
  obtain ⟨K, e, hK⟩ := hf
  obtain ⟨D, d, hD⟩ := hg
  refine ⟨K + D, max e d, fun x => ?_⟩
  have he := (hK x).trans (Nat.mul_le_mul_left K
    (Nat.pow_le_pow_right (by omega : 1 ≤ size x + 1) (le_max_left e d)))
  have hd := (hD x).trans (Nat.mul_le_mul_left D
    (Nat.pow_le_pow_right (by omega : 1 ≤ size x + 1) (le_max_right e d)))
  change f x + g x ≤ (K + D) * (size x + 1) ^ max e d
  rw [Nat.add_mul]
  omega

theorem Bounded.mul {f g : α → ℕ} (hf : Bounded size f) (hg : Bounded size g) :
    Bounded size (fun x => f x * g x) := by
  obtain ⟨K, e, hK⟩ := hf
  obtain ⟨D, d, hD⟩ := hg
  refine ⟨K * D, e + d, fun x => ?_⟩
  calc
    f x * g x ≤ (K * (size x + 1) ^ e) * (D * (size x + 1) ^ d) := Nat.mul_le_mul (hK x) (hD x)
    _ = (K * D) * (size x + 1) ^ (e + d) := by rw [pow_add]; ring

theorem Bounded.pow {f : α → ℕ} (h : Bounded size f) (e : ℕ) :
    Bounded size (fun x => f x ^ e) := by
  induction e with
  | zero => simpa only [pow_zero] using bounded_const (size := size) 1
  | succ e ih => simpa only [pow_succ] using ih.mul h

end NearCubicGates.Adapters.Proximity.Growth
