import Mathlib
import Proof.Wire_3_5.Shared.GF

namespace NearCubicWires.WireExponent3_5.GF2
set_option autoImplicit false

def clmul (x y w : ℕ) : ℕ := (List.range w).foldl (fun acc i => if y.testBit i then acc ^^^ (x <<< i) else acc) 0
def reduce (p ℓ x : ℕ) : ℕ :=
  (List.range ℓ).reverse.foldl (fun acc i => if acc.testBit (i + ℓ) then acc ^^^ (p <<< i) else acc) x
def fmul (p ℓ x y : ℕ) : ℕ := reduce p ℓ (clmul x y ℓ)

/-- Multiplication from LFSR steps and XOR only. -/
def fmulShift (p ℓ x y : ℕ) : ℕ :=
  ((List.range ℓ).foldl (fun (st : ℕ × ℕ) i =>
    (if y.testBit i then st.1 ^^^ st.2 else st.1, lfsr p ℓ st.2)) (0, x)).1

/-- Trace by definition, `Σ_{i<ℓ} a^{2^i}`. -/
def trace (p ℓ a : ℕ) : ℕ :=
  ((List.range ℓ).foldl (fun (st : ℕ × ℕ) _ => (st.1 ^^^ st.2, fmul p ℓ st.2 st.2)) (0, a)).1

def parityMasked (mask a ℓ : ℕ) : ℕ :=
  ((List.range ℓ).filter (fun b => mask.testBit b && a.testBit b)).length % 2

/-- `τ` as a bit mask: `τ_b = Tr(x^b)`. -/
def tau (p ℓ : ℕ) : ℕ := (List.range ℓ).foldl (fun m b => if trace p ℓ (2 ^ b) = 1 then m ||| 2 ^ b else m) 0

/-- `x^4 + x + 1` is primitive (period 15); `x^4+x^3+x^2+x+1` is irreducible but not primitive
(period 5); `x^4 + 1` and `x^4 + x^2 + 1` are reducible (periods 4, 6). -/
theorem periods : period 19 4 = 15 ∧ period 31 4 = 5 ∧ period 17 4 = 4 ∧ period 21 4 = 6 := by decide

theorem mul_shift_eq : ∀ x < 16, ∀ y < 16, fmulShift 19 4 x y = fmul 19 4 x y := by decide

theorem trace_linear : ∀ a < 16, trace 19 4 a = parityMasked (tau 19 4) a 4 := by decide

theorem labels_distinct : ((List.range 15).map (lfsrPow 19 4)).Nodup := by decide

end NearCubicWires.WireExponent3_5.GF2
