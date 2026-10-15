import Proof.Foundations.ProjectionSourceContract
import StatementSupport

/-!
# Binding: CLW20 Lemma 3.10 (the projection PCP, from [BV14]) → `ProjectionPCPSource`

Source PDF: `CLW20_Chen_Lyu_Williams_AE_Circuit_Lower_Bounds_ECCC_TR20-150.pdf`,
PDF page 18 (printed p.17), §3.5, verbatim:

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

The original is BV14 Theorem 1.1 (`BV14_Ben-Sasson_Viola_Short_PCPs_Projection_Queries_ECCC_TR14-017.pdf`,
PDF p.3). It has the same items, with the soundness written as "at most 1/n^10 fraction of the z".

## Deliverables

* `CLW20_Lemma3_10` : the literal. Its hypothesis is that M runs in time `T(n)` on EVERY input
  `(x, y)` with `|x| = n`, for every `y`.
* `CLW20_Lemma3_10_onWitnessLengthT` : the same statement, except that the time hypothesis is
  required only on the inputs the lemma talks about, `y ∈ {0,1}^{T(n)}`. That is the import's
  hypothesis. `clw20_lemma3_10_onWitnessLengthT_to_literal` proves that this version implies the
  literal (the easy direction: a stronger hypothesis is easier to meet).
* `clw20_lemma3_10_onWitnessLengthT_to_import :
  CLW20_Lemma3_10_onWitnessLengthT → ProjectionPCPSource` is PROVED.
* `clw20_lemma3_10_false_at_zero` and `clw20_lemma3_10_onWitnessLengthT_false_at_zero` : if the
  properties are also claimed at `n = 0`, both statements are FALSE. The verifier halts at once
  and `T(n) = n`. Then `T(0) = 0`, and "2^r ≤ T · polylog T" would say `2^r ≤ 0`.

## The gap between the printed hypothesis and the import

The import (`Proof/Foundations/ProjectionSourceContract.lean`) asks M to halt within `T(n)` steps
only when `|w| = T(n)`. The printed hypothesis "running in time T … on inputs of the form (x, y)"
covers every `y`. A verifier may halt on witnesses of length `T(n)` and loop on shorter ones. So
the literal applies to fewer verifiers than the import needs. The missing arrow
`CLW20_Lemma3_10 → CLW20_Lemma3_10_onWitnessLengthT` is a machine wrapper: run M, and reject as
soon as the witness end marker is read. In time `T(n)`, M never reads that marker when the
witness has length `T(n)`. The wrapper is `Bindings/CLW20_Lemma3_10_Wrapper.lean`.

## Differences between the printed lemma and the import, and how each is bridged by proof

1. **Quantifier order and constants.** Printed: `∀ M T`, then "one can output …" with hidden
   constants in "poly(n, log T)", "t = poly(r)" and "T · polylog T". We read every hidden
   constant as chosen after `M` and `T` (the weakest reading), with a separate `K, e` for each
   clause. The import also chooses its algorithm, degrees and coefficient inside the witness,
   after `verifier, T`. The adapter merges the three coefficients into one, `K₀ + K_t + K_p + 1`,
   and keeps the three exponents as the import's `PCPDegrees`.
2. **Soundness: a count against a fraction.** Printed: "at most 2^r/n^10 distinct z". The
   literal is `(#accepting z : ℝ) ≤ 2^r / n^10`. The import bounds `acceptanceFraction ≤ 1/n^10`,
   where `acceptanceFraction = #accepting z / |{0,1}^r|`. `card_bitInput` gives
   `|{0,1}^r| = 2^r`, and dividing by `2^r > 0` is `sound_fraction`.
3. **Projection outputs over the input z of Q.** Printed: `Q : {0,1}^r → {0,1}^{rt}`, with
   "(q1, …, qt) = Q(z)" and "each output bit of Q is a bit of input, the negation of a bit, or a
   constant". The literal has one `ProjectedRandomBit r` for each of the `r·t` output bits of Q.
   Each one is evaluated on Q's own input `z` (the randomness), not on `x`. `q_j` is the `j`-th
   block of `r` bits: output bit `r·j + i` (`blockIndex`). The import instead has
   `queryBits j i : ProjectedRandomBit width` evaluated on the randomness. `toRaw` re-indexes.
   `Circuits.word_eq` proves that the two descriptions list the same projections in the same
   order (`List.ofFn_mul'`).
4. **The proof as a map `{0,1}^r → {0,1}` against a table of `2^r` bits.** Printed: "a map
   π: {0,1}^r → {0,1}". The import's proof is `BitInput (2^r)`, addressed by `binaryAddress`.
   Soundness: every table `p` gives the map `π z = p (binaryAddress z)` with the same accepting
   set, by `rfl`. Completeness: the literal's `π` gives the table
   `a ↦ π (decodeAddress a)`, and `decodeAddress_binaryAddress` shows that the two agree on every
   query.
5. **t = poly(r).** Printed: "for t = poly(r)". The literal is `t ≤ K * (r + 1) ^ e`, the import's
   `queryBound`, for `n ≥ 1`.
6. **Proof length.** Printed: "2^r ≤ T · polylogT". The literal is `2^r ≤ K * T(n) * L(T(n))^e`,
   the import's `proofBound`, with `L = logScale`, the manuscript's `⌈log₂(·+2)⌉ ≥ 1`. Read with
   the plain `log₂`, `polylog T` would vanish at `T = 1`.
7. **Given x (and T(n)).** Printed: "Given x ∈ {0,1}^n, one can output in poly(n, log T) time".
   `T` is an arbitrary function with `T(n) ≥ n`. It is not assumed time-constructible. So the
   algorithm receives `T(n)` in binary with `x`, which is exactly the input whose length
   `poly(n, log T)` measures. With `x` alone the statement can fail, because a `T` that is hard
   to compute cannot then be read off. This is the import's input
   `frame x ++ frame (binary T(n))`. The budget is `K * (n + |binary T(n)| + 1) ^ e`
   (`natBitLength`). Tier 1: the algorithm is an `OrdinaryWordFunction`. Its output word lists
   `r`, `t`, the projection code of every output bit of Q, and R's clauses. It is total on every
   `x`, `n = 0` included, because the import's constructor is total.
8. **n ≥ 1.** The properties are claimed for `n ≥ 1`. At `n = 0` the printed soundness bound
   `2^r/0^10` divides by zero, and "2^r ≤ T · polylog T" is unsatisfiable when `T(0) = 0`
   (proved false above). The import also claims its properties only for `1 ≤ n`.
9. **M and "accepts".** M is the repo's `OrdinaryVerifier`: `x` framed on tape 0 and `y` framed
   on tape 1. "M(x, y) accepts" is `Verifier.accepts`, halting in an accepting control state.
   "If there is a y ∈ {0,1}^{T(n)} such that M(x, y) accepts" is, by definition, the import's
   `verifier.language T n x`.
-/

namespace NearCubicWires.Bindings.CLW20Lemma310

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource NearCubicWires.LocalBitMultitape

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option warningAsError true
set_option maxRecDepth 120000

/-! ## The printed objects -/

/-- The time hypothesis only on the witnesses the lemma talks about, `y ∈ {0,1}^{T(n)}` (the
import's hypothesis). -/
def RunsInTimeOnWitnessLengthT (M : OrdinaryVerifier) (T : ℕ → ℕ) : Prop :=
  ∀ n (x : BitInput n) (y : BitInput (T n)), ∃ receipt,
    run M.machine (T n) (M.inputTapes (List.ofFn x) (List.ofFn y)) = some receipt

/-! ## The literal -/

/-- CLW20 Lemma 3.10 (PDF p.18), with its properties claimed for `n ≥ n₀` and time hypothesis
`runsInTime`. The conjuncts follow the printed order: the algorithm (Tier 1), t = poly(r),
proof length, completeness, soundness. The Complexity item is part of the type `Circuits`. -/
def lemma3_10Core (n₀ : ℕ) (runsInTime : OrdinaryVerifier → (ℕ → ℕ) → Prop) : Prop :=
  ∀ (M : OrdinaryVerifier) (T : ℕ → ℕ), (∀ n, n ≤ T n) → runsInTime M T →
  ∃ out : InputRequest → Circuits,
    -- "Given x ∈ {0,1}^n, one can output in poly(n, log T) time circuits Q … and R" (Tier 1;
    -- the time bound T(n) is supplied in binary)
    (∃ K e : ℕ, Nonempty (OrdinaryWordFunction InputRequest
      (fun x => frame (List.ofFn x.2) ++ frame (T x.1).bits) (fun x => (out x).word)
      (fun x => K * (x.1 + natBitLength (T x.1) + 1) ^ e))) ∧
    -- "for t = poly(r)"
    (∃ K e : ℕ, ∀ x : InputRequest, n₀ ≤ x.1 → (out x).t ≤ K * ((out x).r + 1) ^ e) ∧
    -- "Proof length. 2^r ≤ T · polylogT."
    (∃ K e : ℕ, ∀ x : InputRequest, n₀ ≤ x.1 →
      2 ^ (out x).r ≤ K * T x.1 * logScale (T x.1) ^ e) ∧
    -- "Completeness. If there is a y ∈ {0,1}^{T(n)} such that M(x, y) accepts then there is a
    -- map π: {0,1}^r → {0,1} such that for all z ∈ {0,1}^r, R(π(q1), …, π(qt)) = 1"
    (∀ x : InputRequest, n₀ ≤ x.1 →
      (∃ y : BitInput (T x.1), M.accepts (List.ofFn x.2) (List.ofFn y)) →
      ∃ π : BitInput (out x).r → Bool, ∀ z, (out x).accepts π z = true) ∧
    -- "Soundness. If no y ∈ {0,1}^{T(n)} causes M(x, y) to accept, then for every map π, at most
    -- 2^r/n^10 distinct z ∈ {0,1}^r have R(π(q1), …, π(qt)) = 1"
    (∀ x : InputRequest, n₀ ≤ x.1 →
      (¬ ∃ y : BitInput (T x.1), M.accepts (List.ofFn x.2) (List.ofFn y)) →
      ∀ π : BitInput (out x).r → Bool,
        ((Finset.univ.filter fun z => (out x).accepts π z = true).card : ℝ) ≤
          (2 : ℝ) ^ (out x).r / (x.1 : ℝ) ^ 10)

/-- **CLW20 Lemma 3.10** (PDF p.18), the literal: time `T` on every input `(x, y)`, with the
properties for `n ≥ 1`. -/
def CLW20_Lemma3_10 : Prop :=
  lemma3_10Core 1 RunsInTime

/-- CLW20 Lemma 3.10 with the time hypothesis required only for `y ∈ {0,1}^{T(n)}`. -/
def CLW20_Lemma3_10_onWitnessLengthT : Prop :=
  lemma3_10Core 1 RunsInTimeOnWitnessLengthT

/-- A stronger time hypothesis is easier to meet: the witness-length version implies the
literal. -/
theorem clw20_lemma3_10_onWitnessLengthT_to_literal :
    CLW20_Lemma3_10_onWitnessLengthT → CLW20_Lemma3_10 :=
  fun L M T hT hrun => L M T hT fun n x y => hrun n x (List.ofFn y)

/-! ## The properties cannot also be claimed at `n = 0` -/

/-- A verifier that halts at once and rejects. -/
def haltingVerifier : OrdinaryVerifier where
  tapeCount := 2
  stateCount := 1
  twoTapes := le_rfl
  machine :=
    { descriptionBits := 0
      start := 0
      halted := fun _ => true
      rule := fun _ _ => none }
  accepting := fun _ => false

theorem haltingVerifier_runsInTime : RunsInTime haltingVerifier fun n => n := by
  intro n x y
  cases n <;> exact ⟨_, rfl⟩

theorem lemma3_10Core_false_at_zero (runsInTime : OrdinaryVerifier → (ℕ → ℕ) → Prop)
    (h : runsInTime haltingVerifier fun n => n) : ¬ lemma3_10Core 0 runsInTime := by
  intro L
  obtain ⟨out, _, _, ⟨K, e, hproof⟩, _, _⟩ := L haltingVerifier (fun n => n) (fun _ => le_rfl) h
  have hbound := hproof ⟨0, Fin.elim0⟩ le_rfl
  have hpos : 0 < 2 ^ (out ⟨0, Fin.elim0⟩).r := pow_pos (by norm_num) _
  simp only [Nat.mul_zero, Nat.zero_mul] at hbound
  omega

/-- With the properties claimed at `n = 0` too, the literal is false. -/
theorem clw20_lemma3_10_false_at_zero : ¬ lemma3_10Core 0 RunsInTime :=
  lemma3_10Core_false_at_zero _ haltingVerifier_runsInTime

/-- With the properties claimed at `n = 0` too, the witness-length version is false. -/
theorem clw20_lemma3_10_onWitnessLengthT_false_at_zero :
    ¬ lemma3_10Core 0 RunsInTimeOnWitnessLengthT :=
  lemma3_10Core_false_at_zero _ fun n x y => haltingVerifier_runsInTime n x (List.ofFn y)

/-! ## Bridges -/

/-- The import's record from the printed circuits: query `j`, address bit `i` is output bit
`r·j + i` of Q. -/
def toRaw (P : Circuits) : RawProjectionPCP where
  width := P.r
  queries := P.t
  queryBits := fun j i => P.Q (blockIndex j i)
  decision := P.R

/-- The two descriptions are the same word: the `r·t` output bits of Q in order are the `t`
queries' `r` address bits in order. -/
theorem Circuits.word_eq (P : Circuits) : P.word = (toRaw P).word := by
  unfold Circuits.word RawProjectionPCP.word
  rw [List.ofFn_mul', List.flatten_flatten, List.map_ofFn]
  rfl

/-- The import's table proof, read back as a map on `{0,1}^r`. -/
def decodeAddress {r : ℕ} (a : Fin (2 ^ r)) : BitInput r :=
  fun i => a.val.testBit i.val

theorem decodeAddress_binaryAddress {r : ℕ} (b : BitInput r) :
    decodeAddress (binaryAddress b) = b := by
  have hval : (binaryAddress b).val = Nat.ofBits b := by
    unfold binaryAddress
    change encodeBitInput b % 2 ^ r = Nat.ofBits b
    rw [encodeBitInput_eq_ofBits]
    exact Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow b)
  funext i
  unfold decodeAddress
  rw [hval, Nat.testBit_ofBits_lt _ _ i.isLt]

/-- A table proof `p` accepts on `z` exactly when the map `z ↦ p (binaryAddress z)` does. -/
theorem raw_accepts_eq (P : Circuits) (p : BitInput (2 ^ P.r)) (z : BitInput P.r) :
    (toRaw P).accepts p z = P.accepts (fun w => p (binaryAddress w)) z := rfl

/-- The literal's map `π` as a table gives the same verdicts. -/
theorem raw_accepts_decode (P : Circuits) (π : BitInput P.r → Bool) (z : BitInput P.r) :
    (toRaw P).accepts (fun a => π (decodeAddress a)) z = P.accepts π z := by
  rw [raw_accepts_eq]
  simp only [decodeAddress_binaryAddress]

theorem card_bitInput (r : ℕ) : Fintype.card (BitInput r) = 2 ^ r := by
  simp [BitInput]

/-- "at most 2^r/n^10 distinct z" is "at most a 1/n^10 fraction of the z". -/
theorem sound_fraction (P : Circuits) (p : BitInput (2 ^ P.r)) (n : ℕ)
    (h : ((Finset.univ.filter fun z => P.accepts (fun w => p (binaryAddress w)) z = true).card :
      ℝ) ≤ (2 : ℝ) ^ P.r / (n : ℝ) ^ 10) :
    (toRaw P).acceptanceFraction p ≤ 1 / (n : ℝ) ^ 10 := by
  unfold RawProjectionPCP.acceptanceFraction
  have hcard : (Fintype.card (BitInput (toRaw P).width) : ℝ) = (2 : ℝ) ^ P.r := by
    rw [show (toRaw P).width = P.r from rfl, card_bitInput]
    push_cast
    rfl
  rw [hcard]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ P.r := by positivity
  rw [div_le_iff₀ hpos]
  calc ((Finset.univ.filter fun z => (toRaw P).accepts p z = true).card : ℝ)
      = ((Finset.univ.filter fun z => P.accepts (fun w => p (binaryAddress w)) z = true).card :
          ℝ) := rfl
    _ ≤ (2 : ℝ) ^ P.r / (n : ℝ) ^ 10 := h
    _ = 1 / (n : ℝ) ^ 10 * (2 : ℝ) ^ P.r := by ring

/-- An ordinary word function with a pointwise-equal output word. -/
def congrOutput {Request : Type} {input output output' : Request → List Bool}
    {budget : Request → ℕ} (W : OrdinaryWordFunction Request input output budget)
    (h : ∀ r, output r = output' r) : OrdinaryWordFunction Request input output' budget where
  program := W.program
  realizes := fun r => by
    obtain ⟨receipt, hrun, hout⟩ := W.realizes r
    exact ⟨receipt, hrun, hout.trans (h r)⟩

/-! ## The adapter -/

/-- **CLW20 Lemma 3.10**, with the time hypothesis on `y ∈ {0,1}^{T(n)}`, gives the imported
projection PCP source. -/
theorem clw20_lemma3_10_onWitnessLengthT_to_import :
    CLW20_Lemma3_10_onWitnessLengthT → ProjectionPCPSource := by
  intro L verifier T hT hhalt
  obtain ⟨out, ⟨K0, e0, ⟨W⟩⟩, ⟨Kt, et, ht⟩, ⟨Kp, ep, hp⟩, hcomplete, hsound⟩ :=
    L verifier T hT hhalt
  let K := K0 + Kt + Kp + 1
  refine ⟨{
    output := fun x => toRaw (out x)
    degrees := ⟨e0, et, ep⟩
    coefficient := K
    coefficientPositive := by omega
    constructor := RepairOrdinary.WordFunction.enlargeBudget
      (congrOutput W fun x => Circuits.word_eq (out x))
      (fun x => Nat.mul_le_mul_right _ (by omega))
    proofBound := fun x hx =>
      (hp x hx).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
    queryBound := fun x hx => (ht x hx).trans (Nat.mul_le_mul_right _ (by omega))
    complete := fun x hx hlang => by
      obtain ⟨π, hπ⟩ := hcomplete x hx hlang
      exact ⟨fun a => π (decodeAddress a), fun z => (raw_accepts_decode (out x) π z).trans (hπ z)⟩
    sound := fun x hx hlang p =>
      sound_fraction (out x) p x.1 (hsound x hx hlang fun w => p (binaryAddress w)) }⟩

end NearCubicWires.Bindings.CLW20Lemma310
