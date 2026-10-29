import SourceAdapters.Joins.OrdinaryToTM2
import Bindings.CLW20_Lemma3_9_TM2

/-!
# Dock of the X1 join (`OrdinaryToTM2InTime`) for input 8 (A05)

 ("Full-range amplification interface"): "Initialization, the capped simulation, integer operations,
and reading and writing the framed arities and truth tables all take `2^{O(n)}` time. The usual
polynomial-overhead simulation into TM2 preserves this bound. After increasing its exponent and onset, the bound
is `2^{en}` as required by the companion."

The consumer is `TruthTableConstructionTM2 g` (`Statement.lean:990–996`): one Mathlib machine
`TM2ComputableInTime amplifierInput amplifierOutputWord (fun r => g r.inputArity r.function)` with ONE time
function `M.time : ℕ → ℕ` of the encoded input length, and `M.time (amplifierInput r).length ≤
2^(timeExponent·n)` from an onset. The producer side of A05 is the released ordinary-machine form
`CLW20Lemma39.TruthTableConstruction g` (`Bindings/CLW20_Lemma3_9.lean:104`): a `WordFunction` with an eventually
`2^{O(n)}` budget, finitely many small requests unconstrained.

`tm2Construction_of_ordinary` shows the join delivers exactly that: the ordinary budget is bounded by a function of
the input length, `B(L) = (2(L+1))^U` (`U` = the released `uniformExponent`, which absorbs the finitely many small
requests), the join returns `M` with `M.time L ≤ C·(B L + L + 1)^d` (output cleanup is inside the join's TM2
semantics: `TM2OutputsInTime` with `haltList`), and `L ≤ 2^(n+2)` turns this into `2^((C + d(5U+1))·n)` for
`n ≥ 1`. **DOCK X1-InTime: OK.**
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification

open NearCubicWires NearCubicWires.ExecutableInterfaces NearCubicWires.RepairSource
open NearCubicWires.Bindings.CLW20Lemma39 NearCubicWires.Bindings.CLW20Lemma39TM2
open NearCubicGates.Adapters.Joins

theorem two_pow_le_amplifierInput_length (r : AmplifierRequest) : 2 ^ r.inputArity ≤ (amplifierInput r).length := by
  simp [amplifierInput, boolFunctionTable]

/-- The ordinary budget as a function of the encoded input length. -/
theorem budget_le_length {g : (n : ℕ) → BoolFunction n → AmplifierOutput} (T : TruthTableConstruction g)
    (r : AmplifierRequest) :
    T.budget r ≤ (2 * ((amplifierInput r).length + 1)) ^ uniformExponent T := by
  refine (budget_le_uniform T r).trans ?_
  rw [mul_comm, pow_mul]
  apply Nat.pow_le_pow_left
  have h1 := two_pow_le_amplifierInput_length r
  rcases Nat.eq_zero_or_pos r.inputArity with h0 | h0
  · rw [h0]; simp
  · rw [max_eq_right h0]; omega

/-- The exponential bound on the TM2 time, from the join's polynomial overhead. -/
theorem time_bound_exponential (C d U L n : ℕ) (hU : 1 ≤ U) (hn : 1 ≤ n) (hL : L ≤ 2 ^ (n + 2)) :
    C * ((2 * (L + 1)) ^ U + L + 1) ^ d ≤ 2 ^ ((C + d * (5 * U + 1)) * n) := by
  have hb : 2 ^ (n + 3) ≥ 2 := by
    calc 2 ^ (n + 3) ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 := rfl
  have h1 : 2 * (L + 1) ≤ 2 ^ (n + 4) := by
    have : 2 ^ (n + 4) = 2 * 2 ^ (n + 3) := by rw [pow_succ]; ring
    have : 2 ^ (n + 3) = 2 * 2 ^ (n + 2) := by rw [pow_succ]; ring
    omega
  have h2 : (2 * (L + 1)) ^ U ≤ 2 ^ ((n + 4) * U) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left h1 U
  have h3 : L + 1 ≤ 2 ^ ((n + 4) * U) := by
    have : 2 ^ (n + 4) ≤ 2 ^ ((n + 4) * U) := Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ hU)
    omega
  have h4 : (2 * (L + 1)) ^ U + L + 1 ≤ 2 ^ ((n + 4) * U + 1) := by rw [pow_succ]; omega
  have h5 : ((2 * (L + 1)) ^ U + L + 1) ^ d ≤ 2 ^ (((n + 4) * U + 1) * d) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left h4 d
  have h6 : C ≤ 2 ^ C := (Nat.lt_two_pow_self).le
  have h7 : C + ((n + 4) * U + 1) * d ≤ (C + d * (5 * U + 1)) * n := by
    have : (n + 4) * U + 1 ≤ (5 * U + 1) * n := by nlinarith
    have : ((n + 4) * U + 1) * d ≤ d * (5 * U + 1) * n := by nlinarith
    nlinarith
  calc C * ((2 * (L + 1)) ^ U + L + 1) ^ d ≤ 2 ^ C * 2 ^ (((n + 4) * U + 1) * d) := Nat.mul_le_mul h6 h5
    _ = 2 ^ (C + ((n + 4) * U + 1) * d) := by rw [← pow_add]
    _ ≤ 2 ^ ((C + d * (5 * U + 1)) * n) := Nat.pow_le_pow_right (by norm_num) h7

/-- **Dock X1-InTime.** The X1 join turns the ordinary-machine construction (released Tier 1 form) into exactly the
target's `TruthTableConstructionTM2`. -/
theorem tm2Construction_of_ordinary (hX1 : OrdinaryToTM2InTime) {g : (n : ℕ) → BoolFunction n → AmplifierOutput}
    (T : TruthTableConstruction g) : Nonempty (TruthTableConstructionTM2 g) := by
  obtain ⟨C, d, M, hM⟩ := hX1 amplifierInput amplifierOutputWord (fun r => g r.inputArity r.function) T.budget
    (fun L => (2 * (L + 1)) ^ uniformExponent T) ⟨T.algorithm⟩ (budget_le_length T)
  exact ⟨{ machine := M
           timeExponent := C + d * (5 * uniformExponent T + 1)
           timeOnset := 1
           exponentialTime := fun r hr => (hM _).trans
             (time_bound_exponential C d _ _ _ (one_le_uniformExponent T) hr (amplifierInput_length_le r)) }⟩

end NearCubicGates.Adapters.Amplification
