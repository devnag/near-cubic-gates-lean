import Proof.Gates.Target
import Proof.Foundations.Semantics

/-!
# A weighted symmetric circuit is a symmetric threshold circuit

Paper v2's class 𝒲 (integer top coefficients, arbitrary top function) embeds into the shared
`SymmetricThresholdCircuit` (a function of the number of true bottom gates): a gate with coefficient `a > 0` becomes
`a` copies of itself, and `a < 0` becomes `|a|` copies of its complement, so the count equals the score plus the fixed
offset `N = Σ_{a<0} |a|`. The complement of a real threshold gate is again a real threshold gate on the cube (the
smallest attained value above the reflected threshold). Wires: at most `W (n + 1)`.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Transfer

open NearCubicWires NearCubicGates.Target

variable {n : ℕ}

/-- The reflected linear form `Σ (−w_i) x_i`. -/
noncomputable def negForm (g : RealThresholdGate n) (x : BitInput n) : ℝ :=
  ∑ i, -g.weight i * bitAsReal (x i)

/-- A threshold for the complement gate. -/
noncomputable def complementThreshold (g : RealThresholdGate n) : ℝ := by
  classical
  exact
    let T := (Finset.univ.image (negForm g)).filter (fun v => -g.threshold < v)
    if h : T.Nonempty then T.min' h else -g.threshold + 1

theorem complementThreshold_spec (g : RealThresholdGate n) (x : BitInput n) :
    complementThreshold g ≤ negForm g x ↔ -g.threshold < negForm g x := by
  classical
  unfold complementThreshold
  simp only
  split_ifs with h
  · constructor
    · intro hle
      have hm := Finset.min'_mem _ h
      simp only [Finset.mem_filter] at hm
      linarith [hm.2]
    · intro hlt
      exact Finset.min'_le _ _ (by simp [Finset.mem_filter, hlt])
  · constructor
    · intro hle
      by_contra hc
      push Not at hc
      linarith
    · intro hlt
      exact absurd ⟨negForm g x, by simp [Finset.mem_filter, hlt]⟩ h

/-- The complement gate: weights negated, threshold `complementThreshold`. -/
noncomputable def complementGate (g : RealThresholdGate n) : RealThresholdGate n where
  weight := fun i => -g.weight i
  threshold := complementThreshold g
  support := g.support
  mem_support_iff := fun i => by simp [g.mem_support_iff i]

theorem complementGate_eval (g : RealThresholdGate n) (x : BitInput n) :
    (complementGate g).eval x = !(g.eval x) := by
  have hspec := complementThreshold_spec g x
  have hneg : negForm g x = -∑ i, g.weight i * bitAsReal (x i) := by
    simp [negForm, Finset.sum_neg_distrib, neg_mul]
  unfold RealThresholdGate.eval
  change decide (complementThreshold g ≤ negForm g x) = !decide (g.threshold ≤ _)
  by_cases hc : g.threshold ≤ ∑ i, g.weight i * bitAsReal (x i)
  · have : ¬ complementThreshold g ≤ negForm g x := by rw [hspec, hneg]; linarith
    simp [hc, this]
  · have : complementThreshold g ≤ negForm g x := by rw [hspec, hneg]; push Not at hc; linarith
    simp [hc, this]

/-- The gate whose copies represent coefficient `a_i`. -/
noncomputable def gateFor (C : WeightedSymmetricCircuit n) (i : Fin C.bottomCount) : RealThresholdGate n := by
  classical
  exact if 0 < C.coefficient i then C.bottom i else complementGate (C.bottom i)

/-- `N = Σ_{a<0} |a|`. -/
def negOffset (C : WeightedSymmetricCircuit n) : ℕ :=
  ∑ i, if C.coefficient i < 0 then (C.coefficient i).natAbs else 0

/-- The symmetric threshold circuit with `|a_i|` copies of `gateFor C i`. -/
noncomputable def toSymmetric (C : WeightedSymmetricCircuit n) : SymmetricThresholdCircuit n where
  bottomCount := ∑ i, (C.coefficient i).natAbs
  bottom := fun j => gateFor C (finSigmaFinEquiv.symm j).1
  top := fun count => C.lookup ((count : ℤ) - negOffset C)

theorem count_copies (C : WeightedSymmetricCircuit n) (Q : Fin C.bottomCount → Prop) [DecidablePred Q] :
    ((Finset.univ.filter fun j : Fin (∑ i, (C.coefficient i).natAbs) =>
        Q (finSigmaFinEquiv.symm j).1).card : ℤ) =
      ∑ i, if Q i then ((C.coefficient i).natAbs : ℤ) else 0 := by
  rw [Finset.card_filter]
  push_cast
  rw [Fintype.sum_equiv (finSigmaFinEquiv.symm)
    (fun j => if Q (finSigmaFinEquiv.symm j).1 then (1 : ℤ) else 0) (fun p => if Q p.1 then (1 : ℤ) else 0)
    (fun _ => rfl)]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> simp

theorem toSymmetric_count (C : WeightedSymmetricCircuit n) (x : BitInput n) :
    (((Finset.univ.filter fun i => ((toSymmetric C).bottom i).eval x).card : ℕ) : ℤ) =
      ∑ i, if (gateFor C i).eval x = true then ((C.coefficient i).natAbs : ℤ) else 0 :=
  count_copies C (fun i => (gateFor C i).eval x = true)

theorem toSymmetric_eval (C : WeightedSymmetricCircuit n) (x : BitInput n) :
    (toSymmetric C).eval x = C.eval x := by
  classical
  have hcount := toSymmetric_count C x
  show C.lookup ((((Finset.univ.filter fun i => ((toSymmetric C).bottom i).eval x).card : ℕ) : ℤ) -
      negOffset C) = C.lookup (C.score x)
  rw [hcount]
  congr 1
  unfold negOffset WeightedSymmetricCircuit.score
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hne := C.coefficient_ne_zero i
  unfold gateFor
  by_cases hpos : 0 < C.coefficient i
  · have habs : ((C.coefficient i).natAbs : ℤ) = C.coefficient i := by omega
    simp only [if_pos hpos, show ¬ C.coefficient i < 0 by omega, if_false, sub_zero]
    by_cases hg : (C.bottom i).eval x = true <;> simp [hg, abs_of_pos hpos]
  · have hneg : C.coefficient i < 0 := by omega
    have habs : ((C.coefficient i).natAbs : ℤ) = -C.coefficient i := by omega
    simp only [if_neg hpos, if_pos hneg, complementGate_eval]
    by_cases hg : (C.bottom i).eval x = true <;> simp [hg, abs_of_neg hneg]

theorem toSymmetric_wireCount (C : WeightedSymmetricCircuit n) :
    (toSymmetric C).wireCount ≤ C.topWeight * (n + 1) := by
  unfold SymmetricThresholdCircuit.wireCount WeightedSymmetricCircuit.topWeight
  calc ∑ j, (((toSymmetric C).bottom j).support.card + 1) ≤ ∑ _j : Fin (∑ i, (C.coefficient i).natAbs), (n + 1) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        have := Finset.card_le_univ ((toSymmetric C).bottom j).support
        simp only [Fintype.card_fin] at this
        omega
    _ = (∑ i, (C.coefficient i).natAbs) * (n + 1) := by simp

end NearCubicGates.Close.Transfer
