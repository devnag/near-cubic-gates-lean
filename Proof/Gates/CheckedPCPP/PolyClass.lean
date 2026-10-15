import Mathlib.Tactic

set_option autoImplicit false

namespace NearCubicGates.Close.CheckedPCPP

/-- `f` is at most a fixed polynomial in `S`. -/
def PolyB {ι : Type*} (S : ι → ℕ) (f : ι → ℕ) : Prop := ∃ C e : ℕ, ∀ i, f i ≤ C * (S i + 1) ^ e

/-- A function of one natural number that is at most a fixed polynomial. -/
def PolyF (g : ℕ → ℕ) : Prop := ∃ C e : ℕ, ∀ y, g y ≤ C * (y + 1) ^ e

namespace PolyB

variable {ι : Type*} {S : ι → ℕ}

theorem one_le_pow (x e : ℕ) : 1 ≤ (x + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_pos _)

theorem mono {f g : ι → ℕ} (hg : PolyB S g) (h : ∀ i, f i ≤ g i) : PolyB S f := by
  obtain ⟨C, e, hC⟩ := hg
  exact ⟨C, e, fun i => (h i).trans (hC i)⟩

theorem const (c : ℕ) : PolyB S (fun _ => c) := ⟨c, 0, fun i => by simp⟩

theorem size : PolyB S S := ⟨1, 1, fun i => by simp⟩

theorem add {f g : ι → ℕ} (hf : PolyB S f) (hg : PolyB S g) : PolyB S (fun i => f i + g i) := by
  obtain ⟨C1, e1, h1⟩ := hf
  obtain ⟨C2, e2, h2⟩ := hg
  refine ⟨C1 + C2, e1 + e2, fun i => ?_⟩
  have a1 : (S i + 1) ^ e1 ≤ (S i + 1) ^ (e1 + e2) := Nat.pow_le_pow_right (by omega) (by omega)
  have a2 : (S i + 1) ^ e2 ≤ (S i + 1) ^ (e1 + e2) := Nat.pow_le_pow_right (by omega) (by omega)
  have := h1 i
  have := h2 i
  nlinarith

theorem mul {f g : ι → ℕ} (hf : PolyB S f) (hg : PolyB S g) : PolyB S (fun i => f i * g i) := by
  obtain ⟨C1, e1, h1⟩ := hf
  obtain ⟨C2, e2, h2⟩ := hg
  refine ⟨C1 * C2, e1 + e2, fun i => ?_⟩
  calc f i * g i ≤ (C1 * (S i + 1) ^ e1) * (C2 * (S i + 1) ^ e2) := Nat.mul_le_mul (h1 i) (h2 i)
    _ = C1 * C2 * (S i + 1) ^ (e1 + e2) := by ring

theorem pow {f : ι → ℕ} (hf : PolyB S f) (k : ℕ) : PolyB S (fun i => f i ^ k) := by
  induction k with
  | zero => simpa using const (S := S) 1
  | succ k ih => exact (mul ih hf).mono (fun i => by rw [pow_succ])

/-- Composition with a polynomially bounded function. -/
theorem comp {f : ι → ℕ} (hf : PolyB S f) {g : ℕ → ℕ} (hg : PolyF g) : PolyB S (fun i => g (f i)) := by
  obtain ⟨C, e, hC⟩ := hg
  have h1 : PolyB S (fun i => f i + 1) := add hf (const 1)
  have h2 := pow h1 e
  obtain ⟨C', e', h'⟩ := h2
  exact ⟨C * C', e', fun i => (hC (f i)).trans (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (h' i))⟩

end PolyB

namespace PolyF

theorem of_le {g h : ℕ → ℕ} (hh : PolyF h) (hle : ∀ y, g y ≤ h y) : PolyF g := by
  obtain ⟨C, e, hC⟩ := hh
  exact ⟨C, e, fun y => (hle y).trans (hC y)⟩

theorem toPolyB {g : ℕ → ℕ} (hg : PolyF g) : PolyB (fun y => y) g := hg

end PolyF

end NearCubicGates.Close.CheckedPCPP
