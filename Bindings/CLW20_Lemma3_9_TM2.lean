import Bindings.TuringBridge.Budget
import Bindings.CLW20_Lemma3_9
import StatementSupport

/-!
# Tier 2 binding: CLW20 Lemma 3.9, the truth-table construction in Mathlib's standard model

Source PDF: `CLW20_Chen_Lyu_Williams_AE_Circuit_Lower_Bounds_ECCC_TR20-150.pdf`,
PDF page 18 (printed p.17), §3.4, verbatim (re-extracted for this module):

  "Lemma 3.9 ([STV01]). There is a constant c ≥ 1 such that, for any time-constructible function
  S(n) and every f : {0, 1}^n → {0, 1} that does not have (general) circuits of size S(n). There is
  a function g : {0, 1}^{O(n)} → {0, 1} that cannot be (1/2 + S(n)^{−1/c})-approximated by
  circuits of size S(n)^{1/c}. Furthermore, given the 2^n-length truth table of f, the truth table
  of g can be constructed in 2^{O(n)} time."

## What changes against the Tier 1 literal (`Bindings/CLW20_Lemma3_9.lean`)

ONLY the algorithmic clause of the last sentence. Tier 1 states "the truth table of g can be
constructed in 2^{O(n)} time" as a repo `OrdinaryWordFunction`. Here it is
`TruthTableConstructionTM2`: a Mathlib `Turing.TM2ComputableInTime` machine (a finite multi-stack
Turing machine, `Mathlib/Computability/TuringMachine/Computable.lean`) computing
`f ↦ g` with
* input encoding `amplifierInput` (the framed arity `n`, then the `2^n`-length truth table of
  `f`), the SAME bit word the Tier 1 literal and the import use;
* output encoding `amplifierOutputWord` (the framed arity of `g`, then the full truth table of
  `g`), which is the Tier 1 `truthTableWord` by definition;
* "in 2^{O(n)} time": a constant `timeExponent` and an onset `timeOnset`, with the machine's own
  step bound `time |input|` at most `2^(timeExponent · n)` for `n ≥ timeOnset` (weakest reading,
  as in Tier 1; the onset and the constant may depend on `S`).
Every other clause (`g`, the `O(n)` arity, the inapproximability) is copied verbatim from Tier 1.

"any time-constructible function S(n)" is on the INPUT side (`∀ S`, a hypothesis about `S`), so it
stays the repo's `SourceInterfaces.TimeConstructible` exactly as in Tier 1.

`tier1_of_tier2 : CLW20_Lemma3_9_TM2 → CLW20_Lemma3_9` is proved through the bridge
`tm2ToOrdinaryOutputFree` (`Bindings/TuringBridge/OutputFree.lean`), and composed with the Tier 1 adapter it gives
`clw20_lemma3_9_tm2_to_import : CLW20_Lemma3_9_TM2 → Nonempty SourceAmplifierFactory`.
-/

namespace NearCubicWires.Bindings.CLW20Lemma39TM2

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.Bindings.CLW20Lemma39 NearCubicWires.Bindings.Sim

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option warningAsError true
set_option maxRecDepth 120000

theorem truthTableWord_eq (g : (n : ℕ) → BoolFunction n → AmplifierOutput)
    (request : AmplifierRequest) :
    truthTableWord g request = amplifierOutputWord (g request.inputArity request.function) := rfl

/-! ## Word lengths and exponential arithmetic -/

theorem amplifierInput_length_le (request : AmplifierRequest) :
    (amplifierInput request).length ≤ 2 ^ (request.inputArity + 2) := by
  obtain ⟨n, f⟩ := request
  have hsize : n.bits.length ≤ n := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hn : n < 2 ^ n := Nat.lt_two_pow_self
  have hp : 2 ^ (n + 2) = 4 * 2 ^ n := by rw [pow_add]; ring
  simp only [amplifierInput, List.length_append, RepairOrdinary.frame_length, boolFunctionTable,
    List.length_map, List.length_range]
  omega

/-- The bridge's budget is `2^{O(n)}` from the onset `max timeOnset 1` on. -/
theorem budget_exponential (C e T N n : ℕ) (hn : 1 ≤ n) (hT : T ≤ 2 ^ (e * n))
    (hN : N ≤ 2 ^ (n + 2)) : C * (T + N + 1) ≤ 2 ^ ((3 * C + e + 3) * n) := by
  have h1 : 2 ^ (e * n) ≤ 2 ^ ((e + 3) * n) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h2 : 2 ^ (n + 2) ≤ 2 ^ ((e + 3) * n) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h3 : 1 ≤ 2 ^ ((e + 3) * n) := Nat.one_le_two_pow
  have hsum : T + N + 1 ≤ 3 * 2 ^ ((e + 3) * n) := by omega
  have hC : 3 * C ≤ 2 ^ (3 * C * n) :=
    (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  calc C * (T + N + 1) ≤ C * (3 * 2 ^ ((e + 3) * n)) := Nat.mul_le_mul_left _ hsum
    _ = (3 * C) * 2 ^ ((e + 3) * n) := by ring
    _ ≤ 2 ^ (3 * C * n) * 2 ^ ((e + 3) * n) := Nat.mul_le_mul_right _ hC
    _ = 2 ^ ((3 * C + e + 3) * n) := by rw [← pow_add]; congr 1; ring

/-! ## Tier 2 → Tier 1 -/

/-- The Tier 1 algorithmic clause from the Tier 2 one, through the output-free bridge. -/
noncomputable def TruthTableConstructionTM2.toTier1
    {g : (n : ℕ) → BoolFunction n → AmplifierOutput} (T : TruthTableConstructionTM2 g) :
    TruthTableConstruction g where
  budget := fun request => simConstant T.machine.tm * (maxStmtSize T.machine.tm + 2) *
    (T.machine.time (amplifierInput request).length + (amplifierInput request).length + 1)
  algorithm := tm2ToOrdinaryOutputFree T.machine
  timeExponent := 3 * (simConstant T.machine.tm * (maxStmtSize T.machine.tm + 2)) +
    T.timeExponent + 3
  timeOnset := max T.timeOnset 1
  exponentialTime := fun request hon =>
    budget_exponential _ _ _ _ _ (le_of_max_le_right hon)
      (T.exponentialTime request (le_of_max_le_left hon)) (amplifierInput_length_le request)

/-- The Tier 1 statement for one `c` and `S`, from the Tier 2 one. -/
noncomputable def Lemma3_9AtTM2.toTier1 {c : ℝ} {S : ℕ → ℕ} (W : Lemma3_9AtTM2 c S) :
    Lemma3_9At c S where
  g := W.g
  arityFactor := W.arityFactor
  arityOnset := W.arityOnset
  amplifies := W.amplifies
  construction := W.construction.toTier1

/-- **Tier 2 → Tier 1.** -/
theorem tier1_of_tier2 : CLW20_Lemma3_9_TM2 → CLW20_Lemma3_9 := by
  rintro ⟨c, hc, h⟩
  exact ⟨c, hc, fun S hS => (h S hS).map Lemma3_9AtTM2.toTier1⟩

/-- **Tier 2 → import**, through the Tier 1 adapter (`Bindings/CLW20_Lemma3_9.lean`). -/
theorem clw20_lemma3_9_tm2_to_import : CLW20_Lemma3_9_TM2 → Nonempty SourceAmplifierFactory :=
  fun h => clw20_lemma3_9_to_import (tier1_of_tier2 h)

end NearCubicWires.Bindings.CLW20Lemma39TM2
