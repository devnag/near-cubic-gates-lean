import Mathlib

/-!
# Eventual polynomial bounds in `N` with an explicit exponent

`PE f e`: past an onset, `f N ≤ C (N+1)^e`. The exponent is explicit (it must be fixed before the clock: `sec:gadget-machine`
and the order of constants of `app:multitape`); the constant and the onset are free.
Closure: `const`, `lin`, `raise`, `add`, `mul`, `pow`, `mono`.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith

/-- Eventually `f N ≤ C (N+1)^e`. -/
def PE (f : ℕ → ℕ) (e : ℕ) : Prop := ∃ C onset : ℕ, ∀ N, onset ≤ N → f N ≤ C * (N + 1) ^ e

namespace PE

theorem of_all {f : ℕ → ℕ} {e C : ℕ} (h : ∀ N, f N ≤ C * (N + 1) ^ e) : PE f e := ⟨C, 0, fun N _ => h N⟩

theorem const (c : ℕ) : PE (fun _ => c) 0 := of_all (C := c) (fun N => by simp)

theorem lin : PE (fun N => N + 1) 1 := of_all (C := 1) (fun N => by simp)

theorem mono {f g : ℕ → ℕ} {e : ℕ} (hg : PE g e) (h : ∀ N, f N ≤ g N) : PE f e := by
  obtain ⟨C, o, hC⟩ := hg
  exact ⟨C, o, fun N hN => (h N).trans (hC N hN)⟩

theorem raise {f : ℕ → ℕ} {e e' : ℕ} (hf : PE f e) (he : e ≤ e') : PE f e' := by
  obtain ⟨C, o, hC⟩ := hf
  exact ⟨C, o, fun N hN => (hC N hN).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) he))⟩

theorem add {f g : ℕ → ℕ} {e : ℕ} (hf : PE f e) (hg : PE g e) : PE (fun N => f N + g N) e := by
  obtain ⟨C1, o1, h1⟩ := hf
  obtain ⟨C2, o2, h2⟩ := hg
  refine ⟨C1 + C2, max o1 o2, fun N hN => ?_⟩
  have a := h1 N (le_trans (le_max_left _ _) hN)
  have b := h2 N (le_trans (le_max_right _ _) hN)
  calc f N + g N ≤ C1 * (N + 1) ^ e + C2 * (N + 1) ^ e := Nat.add_le_add a b
    _ = (C1 + C2) * (N + 1) ^ e := by ring

theorem mul {f g : ℕ → ℕ} {e1 e2 : ℕ} (hf : PE f e1) (hg : PE g e2) : PE (fun N => f N * g N) (e1 + e2) := by
  obtain ⟨C1, o1, h1⟩ := hf
  obtain ⟨C2, o2, h2⟩ := hg
  refine ⟨C1 * C2, max o1 o2, fun N hN => ?_⟩
  have a := h1 N (le_trans (le_max_left _ _) hN)
  have b := h2 N (le_trans (le_max_right _ _) hN)
  calc f N * g N ≤ (C1 * (N + 1) ^ e1) * (C2 * (N + 1) ^ e2) := Nat.mul_le_mul a b
    _ = C1 * C2 * (N + 1) ^ (e1 + e2) := by ring

theorem pow {f : ℕ → ℕ} {e : ℕ} (hf : PE f e) (k : ℕ) : PE (fun N => f N ^ k) (e * k) := by
  obtain ⟨C, o, h⟩ := hf
  refine ⟨C ^ k, o, fun N hN => ?_⟩
  calc f N ^ k ≤ (C * (N + 1) ^ e) ^ k := Nat.pow_le_pow_left (h N hN) k
    _ = C ^ k * (N + 1) ^ (e * k) := by rw [mul_pow, ← pow_mul]

theorem cmul {f : ℕ → ℕ} {e : ℕ} (c : ℕ) (hf : PE f e) : PE (fun N => c * f N) e := by
  have := mul (const c) hf
  simpa using this

theorem add_const {f : ℕ → ℕ} {e : ℕ} (hf : PE f e) (c : ℕ) : PE (fun N => f N + c) e :=
  add hf ((const c).raise (Nat.zero_le e))

end PE

end NearCubicGates.Close.WorkerArith
