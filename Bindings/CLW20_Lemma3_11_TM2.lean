import Bindings.TuringBridge.Budget
import Bindings.CLW20_Lemma3_11
import Proof.PCP.PCPPRequestBounds
import StatementSupport

/-!
# Tier 2 binding: CLW20 Lemma 3.11, the two algorithms in Mathlib's standard model

Source PDF: `CLW20_Chen_Lyu_Williams_AE_Circuit_Lower_Bounds_ECCC_TR20-150.pdf`,
PDF page 18 (printed p.17), §3.5, verbatim (re-extracted for this module):

> Lemma 3.11 ([CW19, VW20]). There are constants 0 < s_pcpp < c_pcpp < 1 and a polynomial-time
> transformation that, given a circuit D on n inputs of size m ≥ n, outputs a 2-SAT instance F on
> the variable set Y ∪ Z where |Y| ≤ poly(n), |Z| ≤ poly(m), and the following hold for all
> x ∈ {0, 1}^n:
> • If D(x) = 1, then F|Y=Enc(x) on variable set Z has a satisfying assignment Z_x such that at
>   least c_pcpp-fraction of the clauses are satisfied. Furthermore, there is a poly(m) time
>   algorithm that given x outputs Z_x.
> • If D(x) = 0, then there is no assignment to the Z variables in F|Y=Enc(x) satisfies more than
>   s_pcpp-fraction of the clauses.
> Moreover, the number of clauses in the 2-SAT instance F is a power of 2, and for each
> i ∈ [|Y|], Enc_i(x) is a parity function depending on at most n/2 bits of x.

## What changes against the Tier 1 literal (`Bindings/CLW20_Lemma3_11.lean`)

ONLY the two algorithmic conjuncts of `lemma3_11Core`; everything else (the constants, `F`, the
poly bounds on `|Y|` and `|Z|`, `Z_x`, completeness, soundness, the parity supports, the domain
`n ≥ n₀`, and the two output formats) is copied verbatim.

* "a polynomial-time transformation that, given a circuit D …, outputs … F": a Mathlib
  `Turing.TM2ComputableInPolyTime` machine from the circuit's word `C.word` (the Tier 1 and import
  layout, `natWord n ++ (encodeBooleanCircuit D).bits`) to the output word `outputWord n (F C)`
  (a bit list, output encoding the identity on `List Bool`). Polynomial time is Mathlib's: a
  polynomial in the input length.
* "there is a poly(m) time algorithm that given x outputs Z_x": a Mathlib
  `TM2ComputableInPolyTime` machine on pairs `(D, x)` from `C.word ++ x` to the bits of `Z_x`,
  uniform in `D` exactly as in Tier 1. Its input has length at most `K · (m + 1)^10`
  (`zxInput_length_le`, from the canonical circuit-code bound
  `RecoveryWitnessPolicy.encodeBooleanCircuit_bits_le_parameter` and
  `PCPPRequestBoundary.canonical_circuit_bound`), so polynomial in the input length is
  polynomial in `m`, which is what the Tier 1 budget `K · (m + 1)^e` requires.

`core_tier1_of_tier2 : lemma3_11CoreTM2 n₀ w → lemma3_11Core n₀ w` holds for every domain and
output format (through `tm2Poly_ordinary`, `Bindings/TuringBridge/Budget.lean`). The target form is the explicit-Enc one:
`clw20_lemma3_11_explicitEnc_tm2_to_import : CLW20_Lemma3_11_explicitEnc_TM2 → PointwisePCPPSource`.
At `n₀ = 1` the Tier 2 statement is false for the same reason as Tier 1
(`lemma3_11CoreTM2_false_at_one`).
-/

namespace NearCubicWires.Bindings.CLW20Lemma311TM2

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.Bindings.Sim

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option warningAsError true
set_option maxRecDepth 120000

/-! ## The Tier 2 literal -/

/-- CLW20 Lemma 3.11 with `n ≥ 2` (Tier 2), the output `F`. -/
def CLW20_Lemma3_11_TM2 : Prop := lemma3_11CoreTM2 2 (fun _ F => F.formulaWord)

/-! ## Input lengths are polynomial in the circuit parameters -/

/-- The circuit word has at most `(8192·5^10 + 3) · (m + n + 1)^10` bits. -/
theorem word_length_le (C : Circuit) :
    C.word.length ≤ (8192 * 5 ^ 10 + 3) * (C.m + C.n + 1) ^ 10 := by
  have hbits := (RepairOrdinary.PCPSerializerMass.nat_bits_width (encodeBooleanCircuit C.D)).trans
    ((RecoveryWitnessPolicy.encodeBooleanCircuit_bits_le_parameter C.D
      (parameter := C.m + C.n + 4) (by omega) (by omega) (by unfold Circuit.m; omega)).trans
      (RepairOrdinary.PCPPRequestBoundary.canonical_circuit_bound _))
  have hn : natBitLength C.n ≤ C.n + 1 := by
    unfold natBitLength
    have := Nat.log_le_self 2 C.n
    omega
  have hle : C.m + C.n + 4 + 1 ≤ 5 * (C.m + C.n + 1) := by omega
  have hpow : (C.m + C.n + 4 + 1) ^ 10 ≤ 5 ^ 10 * (C.m + C.n + 1) ^ 10 := by
    rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left hle 10
  have hone : C.m + C.n + 1 ≤ (C.m + C.n + 1) ^ 10 := by
    calc C.m + C.n + 1 = (C.m + C.n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (C.m + C.n + 1) ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
  have hlen : C.word.length = 2 * natBitLength C.n + 1 + (encodeBooleanCircuit C.D).bits.length := by
    simp [Circuit.word, RepairOrdinary.DecompositionSource.natWord_length]
  rw [hlen, Nat.add_mul]
  have h8 : 8192 * (C.m + C.n + 4 + 1) ^ 10 ≤ 8192 * 5 ^ 10 * (C.m + C.n + 1) ^ 10 := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hpow
  omega

/-- The `Z_x` algorithm's input has at most `((8192·5^10 + 3)·2^10 + 1) · (m + 1)^10` bits. -/
theorem zxInput_length_le {n₀ : ℕ} (p : Σ C : CircuitFrom n₀, BitInput C.1.n) :
    (p.1.1.word ++ List.ofFn p.2).length ≤
      ((8192 * 5 ^ 10 + 3) * 2 ^ 10 + 1) * (p.1.1.m + 1) ^ 10 := by
  have hw := word_length_le p.1.1
  have hnm : p.1.1.n ≤ p.1.1.m := p.1.1.sizeAtLeast
  have hle : p.1.1.m + p.1.1.n + 1 ≤ 2 * (p.1.1.m + 1) := by omega
  have hpow : (p.1.1.m + p.1.1.n + 1) ^ 10 ≤ 2 ^ 10 * (p.1.1.m + 1) ^ 10 := by
    rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left hle 10
  have hone : p.1.1.m + 1 ≤ (p.1.1.m + 1) ^ 10 := by
    calc p.1.1.m + 1 = (p.1.1.m + 1) ^ 1 := (pow_one _).symm
      _ ≤ (p.1.1.m + 1) ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : (8192 * 5 ^ 10 + 3) * (p.1.1.m + p.1.1.n + 1) ^ 10 ≤
      (8192 * 5 ^ 10 + 3) * 2 ^ 10 * (p.1.1.m + 1) ^ 10 := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hpow
  simp only [List.length_append, List.length_ofFn]
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-! ## Tier 2 → Tier 1 -/

/-- **Tier 2 → Tier 1**, for every domain `n₀` and every output format. -/
theorem core_tier1_of_tier2 (n₀ : ℕ) (outputWord : (n : ℕ) → Instance n → List Bool) :
    lemma3_11CoreTM2 n₀ outputWord → lemma3_11Core n₀ outputWord := by
  rintro ⟨s, c, hs, hsc, hc1, F, ⟨T⟩, hY, hZ, Zx, hcomplete, ⟨H⟩, hsound, hsupport⟩
  refine ⟨s, c, hs, hsc, hc1, F, ?_, hY, hZ, Zx, hcomplete, ?_, hsound, hsupport⟩
  · exact tm2Poly_ordinary T (fun C => C.1.m + C.1.n) (8192 * 5 ^ 10 + 3) 10
      (fun C => word_length_le C.1)
  · exact tm2Poly_ordinary H (fun p => p.1.1.m) ((8192 * 5 ^ 10 + 3) * 2 ^ 10 + 1) 10
      (fun p => zxInput_length_le p)

theorem tier1_of_tier2 : CLW20_Lemma3_11_TM2 → CLW20_Lemma3_11 :=
  core_tier1_of_tier2 2 _

/-- The target form: explicit-Enc, Tier 2 → Tier 1. -/
theorem explicitEnc_tier1_of_tier2 : CLW20_Lemma3_11_explicitEnc_TM2 → CLW20_Lemma3_11_explicitEnc :=
  core_tier1_of_tier2 2 _

/-- **Tier 2 → import**, through the Tier 1 adapter (`Bindings/CLW20_Lemma3_11.lean`). -/
theorem clw20_lemma3_11_explicitEnc_tm2_to_import :
    CLW20_Lemma3_11_explicitEnc_TM2 → PointwisePCPPSource :=
  fun h => clw20_lemma3_11_explicitEnc_to_import (explicitEnc_tier1_of_tier2 h)

/-- As in Tier 1, the statement on circuits with `n ≥ 1` inputs is false, for every output
format (the counterexample `D(x) = x₁` does not involve the algorithms). -/
theorem lemma3_11CoreTM2_false_at_one (outputWord : (n : ℕ) → Instance n → List Bool) :
    ¬ lemma3_11CoreTM2 1 outputWord :=
  fun h => lemma3_11Core_false_at_one outputWord (core_tier1_of_tier2 1 outputWord h)

end NearCubicWires.Bindings.CLW20Lemma311TM2
