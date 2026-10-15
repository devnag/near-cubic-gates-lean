import Bindings.CLW20_Lemma3_8_Average

/-! # CLW20 Lemma 3.8, Appendix A: the base case and the family closure used by both cases

CLW20 (ECCC TR20-150), Appendix A, PDF p.50, printed p.49:

> "Our proof is by induction on k. The case k = 1 is clearly trivial."

At `k = 1`, `ε_1 = 1/2 − δ`, so a candidate agreeing with `f^{⊕1}` on more than `1/2 + ε_1 = 1 − δ`
of inputs is itself within ℓ1 distance `δ` of `f`: it is the one-term sum `SampleForm.direct`
(`base_case`).

The closure facts come from the definition of a typical class, PDF p.15, printed p.14: "We say a
circuit class C is typical, if given the description of a circuit C of size s, for indices i, j ≤ n
and a bit b, the functions ¬C, C(x_1, ..., x_{i−1}, x_j ⊕ b, x_{i+1}, ..., x_n), and
C(x_1, ..., x_{i−1}, b, x_{i+1}, ..., x_n) all have C circuits of size s". In the import these are
`LiteralProjectionClosed` and `NegationClosedFamily`. `family_xor` is "C or ¬C", `family_one` is the
constant function 1 of Case 2 ("one for the constant function 1"), and `sampledXorSum_lift` carries
a sum obtained at level `k` to level `k + 1` (a `SampleForm` at level `j ≤ k` is one at `j ≤ k + 1`),
which is how Case 1's reduction "to the case of k − 1" returns its answer. -/
namespace NearCubicWires.Bindings.CLW20Lemma38
open NearCubicWires SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem sampleForm_lift {delta : ℚ} {n k : ℕ} {terms : List (ℚ × BoolFunction n)}
    (h : SampleForm delta n k terms) : SampleForm delta n (k + 1) terms := by
  cases h with
  | direct g => exact SampleForm.direct g
  | affine j hj hjk atoms hcount one hone =>
    exact SampleForm.affine j hj (Nat.le_succ_of_le hjk) atoms hcount one hone

def sampledXorSum_lift {family : SizedFunctionFamily} {delta : ℚ} {n k size : ℕ}
    {f : BoolFunction n} (w : SampledXorSum family delta n k size f) :
    SampledXorSum family delta n (k + 1) size f where
  sum := w.sum
  form := sampleForm_lift w.form
  close := w.close

/-- "C or ¬C": xoring a closed family member with a fixed bit stays in the family. -/
theorem family_xor {family : SizedFunctionFamily} (hneg : NegationClosedFamily family)
    {m size : ℕ} {g : BoolFunction m} (hg : family m g size) (b : Bool) :
    family m (fun x => xor b (g x)) size := by
  cases b
  · simpa using hg
  · simpa using hneg g hg

/-- The constant function 1 is in the family at the size of any member. -/
theorem family_one {family : SizedFunctionFamily} (hproj : LiteralProjectionClosed family)
    (hneg : NegationClosedFamily family) {a m size : ℕ} {C : BoolFunction a}
    (hC : family a C size) : family m (fun _ => true) size := by
  have h0 := hproj C hC (fun _ => ProjectedRandomBit.constant (width := m) false)
  have h1 := family_xor (family := family) (size := size) hneg h0 (!C (fun _ => false))
  have heq : (fun x : BitInput m => xor (!C (fun _ => false))
      (C (fun i => (ProjectedRandomBit.constant (width := m) false).eval x))) = fun _ => true := by
    funext x
    cases h : C (fun _ => false) <;> simp [ProjectedRandomBit.eval, h]
  rw [heq] at h1
  exact h1

/-- Case 1's `C′(z) := C(y,z)` is in the family. -/
theorem family_fixFirst {family : SizedFunctionFamily} (hproj : LiteralProjectionClosed family)
    {n k size : ℕ} {C : BoolFunction ((k + 1) * n)} (hC : family ((k + 1) * n) C size)
    (y : BitInput n) : family (k * n) (fun z => C (joinInput y z)) size := by
  have h := hproj C hC (fixFirst (k := k) y)
  have heq : (fun z => C (fun i => (fixFirst (k := k) y i).eval z)) =
      (fun z => C (joinInput y z)) := by
    funext z
    exact congrArg C (fixFirst_eval y z)
  rw [heq] at h
  exact h

/-- Case 2's atom `y ↦ C(y,z_i)` is in the family. -/
theorem family_fixRest {family : SizedFunctionFamily} (hproj : LiteralProjectionClosed family)
    {n k size : ℕ} {C : BoolFunction ((k + 1) * n)} (hC : family ((k + 1) * n) C size)
    (z : BitInput (k * n)) : family n (fun y => C (joinInput y z)) size := by
  have h := hproj C hC (fixRest (n := n) z)
  have heq : (fun y => C (fun i => (fixRest (n := n) z i).eval y)) =
      (fun y => C (joinInput y z)) := by
    funext y
    exact congrArg C (fixRest_eval y z)
  rw [heq] at h
  exact h

theorem xorEpsilon_one (d : ℝ) : xorEpsilon d 1 = 1 / 2 - d := by
  simp [xorEpsilon]

/-- "The case k = 1 is clearly trivial": the reindexed candidate is a `direct` term. -/
theorem base_case (delta : ℚ) {family : SizedFunctionFamily}
    (hproj : LiteralProjectionClosed family) {n : ℕ} (f : BoolFunction n) (size : ℕ)
    (C : BoolFunction (1 * n)) (hC : family (1 * n) C size)
    (hagree : 1 / 2 + xorEpsilon (delta : ℝ) 1 < agreement C (xorPower f 1)) :
    Nonempty (SampledXorSum family delta n 1 size f) := by
  let g : BoolFunction n := fun y => C (oneBlock y)
  have hg : family n g size := hproj C hC (oneBlockProjection n)
  have hagr : agreement g f = agreement C (xorPower f 1) := by
    have h := agreement_comp_equiv (oneBlockEquiv n) C (xorPower f 1)
    have hf : (fun y => xorPower f 1 ((oneBlockEquiv n) y)) = f :=
      funext fun y => xorPower_one f y
    rw [hf] at h
    exact h
  rw [xorEpsilon_one] at hagree
  let s : UnitIntervalCircuitSum family n size :=
    { terms := [(1, g)]
      legal := by
        intro term hterm
        simp only [List.mem_singleton] at hterm
        subst hterm
        exact hg
      inUnitInterval := by
        intro input
        simp only [List.foldl_cons, List.foldl_nil, zero_add, Rat.cast_one, one_mul]
        unfold bitAsReal
        split <;> norm_num }
  have hval : s.value = fun y => bitAsReal (g y) := by
    funext y
    simp [s, UnitIntervalCircuitSum.value]
  refine ⟨{ sum := s, form := SampleForm.direct g, close := ?_ }⟩
  rw [hval, l1_of_boolean, hagr]
  linarith

end NearCubicWires.Bindings.CLW20Lemma38
