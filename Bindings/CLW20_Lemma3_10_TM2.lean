import Bindings.TuringBridge.Budget
import Bindings.CLW20_Lemma3_10
import StatementSupport

/-!
# Tier 2 binding: CLW20 Lemma 3.10, the constructor in Mathlib's standard model

Source PDF: `CLW20_Chen_Lyu_Williams_AE_Circuit_Lower_Bounds_ECCC_TR20-150.pdf`,
PDF page 18 (printed p.17), §3.5, verbatim (re-extracted for this module):

> Lemma 3.10 ([BV14]). Let M be an algorithm running in time T = T(n) ≥ n on inputs of the form
> (x, y) where |x| = n. Given x ∈ {0, 1}^n, one can output in poly(n, log T) time circuits
> Q: {0, 1}^r → {0, 1}^{rt} for t = poly(r) and R: {0, 1}^t → {0, 1} such that:
> • Proof length. 2^r ≤ T · polylogT.
> • Completeness. If there is a y ∈ {0, 1}^{T(n)} such that M(x, y) accepts then there is a map
>   π: {0, 1}^r → {0, 1} such that for all z ∈ {0, 1}^r, R(π(q1), . . . , π(qt)) = 1 where
>   (q1, . . . , qt) = Q(z).
> • Soundness. If no y ∈ {0, 1}^{T(n)} causes M(x, y) to accept, then for every map
>   π: {0, 1}^r → {0, 1}, at most 2^r/n^10 distinct z ∈ {0, 1}^r have R(π(q1), . . . , π(qt)) = 1
>   where (q1, . . . , qt) = Q(z).
> • Complexity. Q is a projection, i.e., each output bit of Q is a bit of input, the negation of a
>   bit, or a constant. R is a 3CNF.

## What changes against the Tier 1 literal (`Bindings/CLW20_Lemma3_10.lean`)

ONLY the OUTPUT-side algorithmic clause, "Given x ∈ {0,1}^n, one can output in poly(n, log T)
time circuits Q … and R": it becomes a Mathlib `Turing.TM2ComputableInPolyTime` machine with the
SAME input word as Tier 1 and the import (`frame x ++ frame (binary T(n))`; `T` is not assumed
time-constructible, so `T(n)` is supplied in binary, Tier 1 item 7) and the SAME output word
`Circuits.word` (output encoding the identity on `List Bool`). Polynomial time in Mathlib's sense
is polynomial in the input length `2n + 2·|binary T(n)| + 2`, i.e. `poly(n, log T)`.

The verifier `M` and its time hypothesis `RunsInTime` stay in the repo's model, as in Tier 1:
they are on the INPUT side of the lemma (`∀ M T`, hypotheses about `M`). Restating them in
Mathlib's model would need the REVERSE simulation (our bit machine inside a TM2 machine), which
is not part of this bridge. Every other clause (`t = poly(r)`, proof length, completeness,
soundness, the Complexity item in the type `Circuits`, `n ≥ 1`) is copied verbatim.

`tier1_of_tier2 : CLW20_Lemma3_10_TM2 → CLW20_Lemma3_10` is proved through `tm2Poly_ordinary`
(`Bindings/TuringBridge/Budget.lean`). Composed with
`CLW20Lemma310Guard.clw20_lemma3_10_to_import : CLW20_Lemma3_10 → ProjectionPCPSource`
it gives the import.
-/

namespace NearCubicWires.Bindings.CLW20Lemma310TM2

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource NearCubicWires.LocalBitMultitape
open NearCubicWires.Bindings.CLW20Lemma310 NearCubicWires.Bindings.Sim

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option warningAsError true
set_option maxRecDepth 120000

/-- The constructor's input word has length at most `2 · (n + natBitLength (T n) + 1)`. -/
theorem input_length_le (T : ℕ → ℕ) (x : InputRequest) :
    (frame (List.ofFn x.2) ++ frame (T x.1).bits).length ≤
      2 * (x.1 + natBitLength (T x.1) + 1) ^ 1 := by
  have hbits : (T x.1).bits.length ≤ natBitLength (T x.1) := by
    rw [Nat.size_eq_bits_len]
    unfold natBitLength
    exact Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by norm_num) _)
  simp only [List.length_append, RepairOrdinary.frame_length, List.length_ofFn, pow_one]
  omega

/-- **Tier 2 → Tier 1**, for every onset `n₀` and time hypothesis. -/
theorem core_tier1_of_tier2 (n₀ : ℕ) (runsInTime : OrdinaryVerifier → (ℕ → ℕ) → Prop) :
    lemma3_10CoreTM2 n₀ runsInTime → lemma3_10Core n₀ runsInTime := by
  intro L M T hT hrun
  obtain ⟨out, ⟨H⟩, ht, hproof, hcomplete, hsound⟩ := L M T hT hrun
  exact ⟨out, tm2Poly_ordinary H (fun x => x.1 + natBitLength (T x.1)) 2 1
    (input_length_le T), ht, hproof, hcomplete, hsound⟩

/-- **Tier 2 → Tier 1** for the literal. -/
theorem tier1_of_tier2 : CLW20_Lemma3_10_TM2 → CLW20_Lemma3_10 :=
  core_tier1_of_tier2 1 RunsInTime

end NearCubicWires.Bindings.CLW20Lemma310TM2
