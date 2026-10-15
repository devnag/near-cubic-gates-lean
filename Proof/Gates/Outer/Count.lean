import Proof.Gates.Outer.Circuit

/-!
# Counting through the truncation `r ↦ r|_ℓ`

`card_trunc`: for `ℓ ≤ q`, the `r ∈ {0,1}^q` whose first `ℓ` bits satisfy a predicate number `2^{q−ℓ}` times the
`z ∈ {0,1}^ℓ` that satisfy it. Used for the outer soundness bound (paper §11.4: `D_B` "ignores its last q − ℓ_out
inputs", so the fraction of seeds it accepts is the fraction of `C`'s unsatisfying assignments).
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Outer

open NearCubicWires

variable {q ℓ : ℕ}

/-- `{0,1}^q ≃ {0,1}^ℓ × {0,1}^{q−ℓ}`, first component the truncation. -/
def splitEquiv (h : ℓ ≤ q) : BitInput q ≃ BitInput ℓ × BitInput (q - ℓ) where
  toFun r := (truncInput r, fun j => r ⟨ℓ + j.val, by omega⟩)
  invFun p := fun i => if hi : i.val < ℓ then p.1 ⟨i.val, hi⟩ else p.2 ⟨i.val - ℓ, by omega⟩
  left_inv r := by
    funext i
    by_cases hi : i.val < ℓ
    · simp [hi, truncInput, show i.val < q from i.isLt]
    · simp only [hi, dite_false]
      congr 1
      ext
      simp
      omega
  right_inv p := by
    rcases p with ⟨z, w⟩
    refine Prod.ext ?_ ?_
    · funext i
      simp [truncInput, show i.val < q by omega]
    · funext j
      simp

theorem card_trunc (h : ℓ ≤ q) (f : BitInput ℓ → Prop) [DecidablePred f] :
    (Finset.univ.filter fun r : BitInput q => f (truncInput r)).card =
      2 ^ (q - ℓ) * (Finset.univ.filter fun z : BitInput ℓ => f z).card := by
  classical
  have h1 : (Finset.univ.filter fun r : BitInput q => f (truncInput r)).card =
      (Finset.univ.filter fun p : BitInput ℓ × BitInput (q - ℓ) => f p.1).card := by
    apply Finset.card_bij (fun r _ => splitEquiv h r)
    · intro r hr
      simpa [splitEquiv] using hr
    · intro a _ b _ hab
      exact (splitEquiv h).injective hab
    · intro p hp
      refine ⟨(splitEquiv h).symm p, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      have : truncInput ((splitEquiv h).symm p) = p.1 := by
        have := congrArg Prod.fst ((splitEquiv h).apply_symm_apply p)
        simpa [splitEquiv] using this
      rw [this]
      exact hp
  rw [h1]
  have h2 : (Finset.univ.filter fun p : BitInput ℓ × BitInput (q - ℓ) => f p.1) =
      (Finset.univ.filter fun z : BitInput ℓ => f z) ×ˢ (Finset.univ : Finset (BitInput (q - ℓ))) := by
    ext p
    simp
  rw [h2, Finset.card_product, Finset.card_univ]
  simp [BitInput, Nat.mul_comm]

end NearCubicGates.Close.Outer
