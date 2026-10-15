import Statement

/-! # The circuit class contains every SYM∘THR circuit, and W bounds the gate count

A check of `WeightedSymmetricCircuit` in the trusted statement against the paper's class `𝒲`
(`paper/paper.tex:177-190`, `def:class`) and the remark after it (`paper/paper.tex:192-200`): bottom
gates are threshold gates `[∑ aᵢ xᵢ ≥ t]` with arbitrary real `aᵢ, t` and unrestricted fan-in, top
coefficients are nonzero integers charged by `W(C) = ∑ |wᵢ|`, and the output lookup `f : ℤ → {0,1}` is
arbitrary. `SourceMapping/main-theorem.md` (items 2 and 3) compares the definitions line by line.

A lower bound is only as strong as the class it quantifies over. A skeptic should ask whether the Lean class
silently omits circuits the paper covers, and whether a budget on `W` really bounds the number of gates.
This module proves:

* `every_threshold_is_a_gate`: every real threshold function on `n` inputs is a bottom gate of the class.
* `symThr`, `symThr_topWeight`, `symThr_eval`: an ordinary SYM∘THR circuit (`G` gates, one top wire each,
  an arbitrary symmetric output on the number of gates that fire) is a member with `W = G`, so the
  theorem is a gate lower bound for SYM∘THR, as the abstract and `paper/paper.tex:198-199` state.
* `bottomCount_le_topWeight`: in every member the number of bottom gates is at most `W`.
-/

namespace NearCubicGates.StatementChecks.CircuitClass

open NearCubicGates.Target NearCubicWires
open scoped BigOperators

set_option autoImplicit false

/-- Every real threshold function `x ↦ [t ≤ ∑ aᵢ xᵢ]` is computed by a gate of the class. -/
theorem every_threshold_is_a_gate {n : ℕ} (a : Fin n → ℝ) (t : ℝ) :
    ∃ g : RealThresholdGate n, ∀ x, g.eval x = decide (t ≤ ∑ i, a i * bitAsReal (x i)) := by
  classical
  exact ⟨⟨a, t, Finset.univ.filter (fun i => a i ≠ 0), by simp⟩, fun _ => rfl⟩

/-- An ordinary SYM∘THR circuit: `G` threshold gates, unit top wires, and the output `f` applied to the
number of gates that fire. -/
def symThr {n G : ℕ} (g : Fin G → RealThresholdGate n) (f : ℕ → Bool) :
    WeightedSymmetricCircuit n where
  bottomCount := G
  bottom := g
  coefficient := fun _ => 1
  coefficient_ne_zero := fun _ => one_ne_zero
  lookup := fun z => f z.toNat

/-- The top weight of an ordinary SYM∘THR circuit is its number of gates. -/
theorem symThr_topWeight {n G : ℕ} (g : Fin G → RealThresholdGate n) (f : ℕ → Bool) :
    (symThr g f).topWeight = G := by
  show (∑ _i : Fin G, ((1 : ℤ)).natAbs) = G
  simp

/-- An ordinary SYM∘THR circuit outputs `f` of the number of gates that fire. -/
theorem symThr_eval {n G : ℕ} (g : Fin G → RealThresholdGate n) (f : ℕ → Bool) (x : BitInput n) :
    (symThr g f).eval x = f (∑ i : Fin G, if (g i).eval x = true then 1 else 0) := by
  show f (∑ i : Fin G, (1 : ℤ) * (if (g i).eval x = true then 1 else 0)).toNat = _
  congr 1
  simp only [one_mul]
  rw [show (∑ i : Fin G, (if (g i).eval x = true then (1 : ℤ) else 0))
      = ((∑ i : Fin G, (if (g i).eval x = true then 1 else 0) : ℕ) : ℤ) by push_cast; rfl]
  exact Int.toNat_natCast _

/-- Every member has at most `W(C)` bottom gates, because every top coefficient is a nonzero integer. -/
theorem bottomCount_le_topWeight {n : ℕ} (C : WeightedSymmetricCircuit n) :
    C.bottomCount ≤ C.topWeight := by
  unfold WeightedSymmetricCircuit.topWeight
  calc C.bottomCount = ∑ _i : Fin C.bottomCount, 1 := by simp
    _ ≤ ∑ i, (C.coefficient i).natAbs := by
        apply Finset.sum_le_sum
        intro i _
        exact Int.natAbs_pos.mpr (C.coefficient_ne_zero i)

end NearCubicGates.StatementChecks.CircuitClass
