import Proof.Foundations.SourceInterfaces
import StatementSupport

/-!
# Binding: CTW26 Lemma 3.2 (attributed there to [MTT61]) → `ThresholdNormalizationContract`

Source PDF: `CTW26_Chen_Tal_Wang_Superquadratic_THR_THR_Lower_Bounds_ECCC_TR26-039.pdf`.

* PDF page 9 (printed p.7), §3 Preliminaries:
  "For any mathematical statement α, let I[α] be the indicator that α holds, i.e., it equals 1
  if α holds and 0 otherwise."
* PDF page 9, Definition 3.1 (Gates): "We define the following gates we will use. (on input
  (x1, x2, · · · , xm) ∈ {0, 1}^m)" and the bullet
  "THR: This gate has parameters w1, w2, · · · , wm, t ∈ R, and outputs
  I[w1x1 + w2x2 + · · · + wmxm ≥ t]. (Replacing ≥ by >, < or ≤ gives the same definition.)"
* PDF page 10 (printed p.8), Lemma 3.2 ([MTT61]):
  "For any THR gate on m input bits, there is an equivalent THR gate where all parameters are
  integers in range ±m^m."

Transcription choices (all literal, nothing hidden):
* The input bits are real numbers `x i ∈ {0, 1}`, so the weighted sum is the printed real sum.
* "equivalent" = the two gates give the same output on every input in `{0,1}^m`.
* "all parameters" = every weight `w i` AND the threshold `t` (Definition 3.1 lists both as
  parameters). "integers in range ±m^m" = each is an integer `k` with `-m^m ≤ k ≤ m^m`.
* `m` ranges over EVERY natural number, including `m = 0`, where Lean's `0 ^ 0 = 1`.
  `ctw26_lemma3_2_at_zero` proves the literal instance at `m = 0` outright, and
  `ctw26_at_zero_needs_zero_pow_zero_eq_one` shows that the reading `0^0 = 0` would make that
  instance false, so the convention matters and the one used is the true one.
* The adapter checks the conventions of `Proof/Foundations/Semantics.lean`: `RealThresholdGate.eval` and
  `NormalizedThresholdGate.eval` both use `threshold ≤ sum` (the printed `≥ t`), and
  `parametersBoundedBy` bounds the weights and the threshold. The import is stated for
  `0 < m` only, so the adapter just restricts.
-/

namespace NearCubicWires.Bindings.CTW26

open NearCubicWires NearCubicWires.SourceInterfaces
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option warningAsError true
set_option maxRecDepth 120000

theorem I_eq_I_iff {p q : Prop} [Decidable p] [Decidable q] : I p = I q ↔ (p ↔ q) := by
  unfold I
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- Sanity: the literal statement holds at the edge `m = 0` (where `0 ^ 0 = 1`). -/
theorem ctw26_lemma3_2_at_zero (g : THRGate 0) :
    ∃ h : THRGate 0,
      Equivalent g h ∧
        (∀ i, IsIntegerInRange (h.w i) (0 ^ 0)) ∧ IsIntegerInRange h.t (0 ^ 0) := by
  by_cases ht : g.t ≤ 0
  · refine ⟨⟨fun i => i.elim0, 0⟩, ?_, fun i => i.elim0, ⟨0, by simp, by simp, by simp⟩⟩
    intro x _
    unfold THRGate.output
    rw [I_eq_I_iff]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, ge_iff_le]
    exact ⟨fun _ => le_refl 0, fun _ => ht⟩
  · refine ⟨⟨fun i => i.elim0, 1⟩, ?_, fun i => i.elim0, ⟨1, by simp, by simp, by simp⟩⟩
    intro x _
    unfold THRGate.output
    rw [I_eq_I_iff]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, ge_iff_le]
    constructor
    · intro h
      exact absurd h ht
    · intro h
      norm_num at h

/-- Why the `0 ^ 0 = 1` convention matters: with bound `0` (the reading `0 ^ 0 = 0`) the
constant-false gate on zero inputs has no equivalent gate, because the only allowed threshold
`0` makes the empty sum `0 ≥ 0` true. -/
theorem ctw26_at_zero_needs_zero_pow_zero_eq_one :
    ¬ ∃ h : THRGate 0,
      Equivalent ⟨fun i => i.elim0, 1⟩ h ∧ IsIntegerInRange h.t 0 := by
  rintro ⟨h, hequiv, k, hk, hk1, hk2⟩
  have hk0 : k = 0 := by push_cast at hk1 hk2; omega
  have hx : IsInput (fun i : Fin 0 => i.elim0) := fun i => i.elim0
  have := hequiv _ hx
  unfold THRGate.output at this
  rw [I_eq_I_iff] at this
  simp only [Finset.univ_eq_empty, Finset.sum_empty, ge_iff_le] at this
  rw [hk, hk0] at this
  norm_num at this

/-- Every Boolean input, read through `bitAsReal` (Proof/Foundations/Semantics.lean), is an input of `{0,1}^m`. -/
theorem isInput_bitAsReal {m : ℕ} (input : BitInput m) :
    IsInput (fun i => bitAsReal (input i)) := by
  intro i
  unfold bitAsReal
  cases input i <;> simp

/-- **Adapter.** The literal CTW26 Lemma 3.2 implies the imported
`SourceInterfaces.ThresholdNormalizationContract` (which is the same statement for `0 < m`, on
Boolean inputs, with integer-typed parameters). -/
theorem ctw26_to_import : CTW26_Lemma3_2 → ThresholdNormalizationContract := by
  intro hlit m _ gate
  obtain ⟨h, hequiv, hw, ht⟩ := hlit m ⟨gate.weight, gate.threshold⟩
  choose k hk using hw
  obtain ⟨c, hc, hc1, hc2⟩ := ht
  refine ⟨⟨k, c⟩, ?_, ?_, ?_⟩
  · intro input
    have heq := hequiv _ (isInput_bitAsReal input)
    unfold THRGate.output at heq
    rw [I_eq_I_iff] at heq
    simp only [ge_iff_le] at heq
    have hcast :
        (((∑ i, k i * (if input i then 1 else 0) : ℤ)) : ℝ) =
          ∑ i, h.w i * bitAsReal (input i) := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [(hk i).1]
      unfold bitAsReal
      cases input i <;> simp
    show decide (c ≤ ∑ i, k i * (if input i then 1 else 0)) =
      decide (gate.threshold ≤ ∑ i, gate.weight i * bitAsReal (input i))
    rw [decide_eq_decide, ← Int.cast_le (R := ℝ), hcast, ← hc]
    exact heq.symm
  · intro i
    show Int.natAbs (k i) ≤ m ^ m
    have h1 := (hk i).2.1
    have h2 := (hk i).2.2
    omega
  · show Int.natAbs c ≤ m ^ m
    omega

end NearCubicWires.Bindings.CTW26
