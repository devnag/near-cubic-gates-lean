import Proof.Foundations.RepresentationSourceContracts
import StatementSupport

/-!
# Binding: CLW20 Lemma 3.11 (the two-query PCPP, from [CW19, VW20]) → `PointwisePCPPSource`

Source PDF: `CLW20_Chen_Lyu_Williams_AE_Circuit_Lower_Bounds_ECCC_TR20-150.pdf`,
PDF page 18 (printed p.17), §3.5, verbatim:

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

## Deliverables

* `CLW20_Lemma3_11_asPrinted` : the sentence above for EVERY `n ≥ 1`.
  `clw20_lemma3_11_asPrinted_false` : it is FALSE. The proof uses `n = 1` and `D(x) = x₁`.
  Each `Enc_i` depends on at most `⌊1/2⌋ = 0` bits, so it is constant. Then `F|Y=Enc(x)` is the
  same instance for `x = 0` and `x = 1`, and completeness at `x = 1` contradicts soundness at
  `x = 0`, because `s < c`. `lemma3_11Core_false_at_one` proves this for EVERY output format, so
  the explicit-Enc reading below is false at `n = 1` as well.
* `CLW20_Lemma3_11` : the printed sentence with the ONLY change `n ≥ 2`.
  Support for `n ≥ 2`: CW19 Lemma 27 (`CW19_Chen_Williams_Stronger_Connections_via_PCPP.pdf`,
  PDF page 16) builds the code as "Enc(x) := Enc′(x1) ◦ Enc′(x2) ◦ Enc′(x3)", where x1, x2, x3 each
  have length "between ⌊n/3⌋ and ⌈n/3⌉". So each code bit is a parity of at most `⌈n/3⌉` input bits,
  and `⌈n/3⌉ ≤ ⌊n/2⌋` for every `n ≠ 1`, in particular for every `n ≥ 2` (`ceil_third_le_floor_half`). The printed Lemma 27 also
  says "at most n/2 bits", and at `n = 1` that fails in the same way.
* `CLW20_Lemma3_11_explicitEnc` : `CLW20_Lemma3_11` with ONE documented addition: the
  transformation's output word also lists the support of every `Enc_i`. That is the import's
  `pcppOutput` format. Every other clause is the same (both are `lemma3_11Core 2 _`, which differ
  only in the output-word argument).
  `clw20_lemma3_11_explicitEnc_to_import : CLW20_Lemma3_11_explicitEnc → PointwisePCPPSource`
  is PROVED.

## The gap between the literal and the import

The import's `constructor` must output `pcppOutput r (output r)`. The middle block of that word
is the support bitmap of every systematic coordinate. The printed lemma says that the
transformation "outputs a 2-SAT instance F". It never says that `Enc` is output or computable.
The supports cannot be recovered from `F`, from `Z_x`, or from the gap. So `CLW20_Lemma3_11`,
read literally, does not give the import. The textual basis for the one-field addition is:
* CLW20 PDF p.28 (printed p.27), §6.2.1: "Recall that Enc : {0, 1}^ℓ → {0, 1}^|Y| is the fixed
  F2-linear error correcting code used in Lemma 3.11." In the validity test PDF p.29 (printed p.28) says
  "Enc_s(x) depends on at most ℓ/2 bits (the moreover part of Lemma 3.11). We can then enumerate
  all these bits". So the paper's own algorithm knows the supports.
* CW19 Lemma 27, PDF p.16: "a constant-rate linear error correcting code ECC with minimum relative
  distance δ, an efficient encoder Enc and an efficient decoder Dec". A linear code with an
  efficient encoder has computable supports: `j ∈ supp(Enc_i)` iff `Enc(e_j)_i = 1`.
The arrow `CLW20_Lemma3_11 → CLW20_Lemma3_11_explicitEnc` needs an ordinary machine that also
writes the supports. That machine is not formalized here.

## Transcription choices (everything is in the literal's type or recorded here)

* The circuits are the repo's `BooleanCircuit n` (topological fan-in-two DAG). The size is
  `m = D.size`, the number of nodes. The domain is `n₀ ≤ n ≤ m`.
* The objects "F on Y ∪ Z" and `Enc` are `Instance n`. `F` has `|Y| + |Z|` variables, and the
  Y variables are the indices below `|Y|`. Its clauses are ORs of two literals (the repo's
  `TwoLiteralClause`). The clauses are indexed by `Fin (2 ^ clauseBits)`: this is the printed
  "the number of clauses … is a power of 2". "Enc_i(x) is a parity function" means that
  `Enc_i(x) = parityOn (encSupport i) x`, the XOR of the bits in the support. The parity depends
  on exactly the bits of its support, so "depending on at most n/2 bits" is
  `(encSupport i).card ≤ n / 2`. Here `/` is ℕ-division (floor). This is exact, not a choice,
  because a count of bits is an integer. The import has the same bound
  (`SourceInterfaces.PointwisePCPP.systematicSupportBound`). `Enc` may depend on `D`. That is
  the weakest reading, because the sentence does not fix `Enc` before `D`.
* "F|Y=Enc(x) … fraction of the clauses satisfied" is `Instance.fraction`. It sets the Y
  variables to `Enc(x)` and the Z variables to `z` (`Fin.addCases`), counts the satisfied
  clauses, and divides by `2 ^ clauseBits`. It is the same term as
  `PointwisePCPP.satisfiedFraction` (Proof/Foundations/SourceInterfaces.lean).
* Quantifier order as printed: first `∃ s c` with `0 < s < c < 1`, then the transformation
  (`F`, with its machine), then the polynomials. The polynomials are hidden constants, so they
  come after the transformation and may depend on it. That is the weakest reading. "poly(n)" is
  `K * (n + 1) ^ e` and "poly(m)" is `K * (m + 1) ^ e`, with a separate `K, e` for each clause.
* Tier 1 machine model. "a polynomial-time transformation that, given a circuit D, … outputs F"
  is an `OrdinaryWordFunction` over the circuits. It reads the circuit in the repo's canonical
  word `natWord n ++ (encodeBooleanCircuit D).bits` (the import's `pcppInput`), and it runs within
  `K * (m + n + 1) ^ e` steps (polynomial in the circuit parameters; `m ≥ n`). The output word is
  an argument of `lemma3_11Core`: `Instance.formulaWord` (F only, the literal) or
  `Instance.formulaEncWord` (F plus Enc's supports, the import's `pcppOutput` layout).
  "there is a poly(m) time algorithm that given x outputs Z_x" is ONE `OrdinaryWordFunction` on
  pairs `(D, x)`, within `K * (m + 1) ^ e` steps, whose output word is the bit list of `Z_x`.
  It is uniform in `D`. If the algorithm could depend on `D`, the clause would say nothing,
  because a machine built for one fixed `D` can compute any function of `x` by table lookup in
  linear time. CLW20 uses `Z_x` as efficiently computable, so the uniform reading is the
  faithful one. Tier 2 replaces only these two conjuncts.
* Proved, not assumed: the import's `clauseCountBound` (`2 ^ clauseBits ≤ poly(m)`) is not
  printed. It follows from the transformation's step bound. The output tape of an ordinary
  run holds at most `steps` cells (`output_length_le_budget`), and the output word lists
  `2 · 2^clauseBits` numbers, each at least one bit long (`two_pow_le_formulaEncWord_length`).
-/

namespace NearCubicWires.Bindings.CLW20Lemma311

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.LocalBitMultitape
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option warningAsError true
set_option maxRecDepth 120000

/-! ## The printed objects -/

/-- Tier 1 output word of the literal: `F` alone (the counts, then every clause as two literal
indices). -/
def Instance.formulaWord {n : ℕ} (F : Instance n) : List Bool :=
  natListWord [F.Ybits, F.Zbits, F.clauseBits] ++
    natListWord ((List.ofFn fun i : Fin (2 ^ F.clauseBits) =>
      [literalIndex (F.clauses i).left, literalIndex (F.clauses i).right]).flatten)

/-! ## The literal -/

/-- CLW20 Lemma 3.11 (PDF p.18) on circuits with at least `n₀` inputs, with the
transformation's output word `outputWord`. The conjuncts follow the printed order:
constants; transformation (Tier 1); |Y| ≤ poly(n); |Z| ≤ poly(m); completeness; the poly(m)
algorithm for `Z_x` (Tier 1); soundness; Enc_i depends on at most n/2 bits.
"the number of clauses is a power of 2" is part of the type `Instance`. -/
def lemma3_11Core (n₀ : ℕ) (outputWord : (n : ℕ) → Instance n → List Bool) : Prop :=
  ∃ s c : ℝ, 0 < s ∧ s < c ∧ c < 1 ∧
  ∃ F : (C : CircuitFrom n₀) → Instance C.1.n,
    -- "a polynomial-time transformation that, given a circuit D …, outputs … F" (Tier 1)
    (∃ K e : ℕ, Nonempty (OrdinaryWordFunction (CircuitFrom n₀)
      (fun C => C.1.word) (fun C => outputWord C.1.n (F C))
      (fun C => K * (C.1.m + C.1.n + 1) ^ e))) ∧
    -- "|Y| ≤ poly(n)"
    (∃ K e : ℕ, ∀ C, (F C).Ybits ≤ K * (C.1.n + 1) ^ e) ∧
    -- "|Z| ≤ poly(m)"
    (∃ K e : ℕ, ∀ C, (F C).Zbits ≤ K * (C.1.m + 1) ^ e) ∧
    ∃ Zx : (C : CircuitFrom n₀) → BitInput C.1.n → BitInput (F C).Zbits,
      -- "If D(x) = 1, then F|Y=Enc(x) … has … Z_x such that at least c-fraction of the clauses
      -- are satisfied."
      (∀ C x, C.1.D.eval x = true → (F C).fraction x (Zx C x) ≥ c) ∧
      -- "there is a poly(m) time algorithm that given x outputs Z_x" (Tier 1)
      (∃ K e : ℕ, Nonempty (OrdinaryWordFunction (Σ C : CircuitFrom n₀, BitInput C.1.n)
        (fun p => p.1.1.word ++ List.ofFn p.2) (fun p => List.ofFn (Zx p.1 p.2))
        (fun p => K * (p.1.1.m + 1) ^ e))) ∧
      -- "If D(x) = 0, then there is no assignment to the Z variables in F|Y=Enc(x) [that]
      -- satisfies more than s-fraction of the clauses."
      (∀ C x, C.1.D.eval x = false → ∀ z, (F C).fraction x z ≤ s) ∧
      -- "for each i ∈ [|Y|], Enc_i(x) is a parity function depending on at most n/2 bits of x"
      (∀ C i, ((F C).encSupport i).card ≤ C.1.n / 2)

/-- **(a)** CLW20 Lemma 3.11 as printed (PDF p.18), for every `n ≥ 1`. The output is `F`. -/
def CLW20_Lemma3_11_asPrinted : Prop :=
  lemma3_11Core 1 (fun _ F => F.formulaWord)

/-- **(c)** CLW20 Lemma 3.11 (PDF p.18) with the ONLY change `n ≥ 2`. The support for
`n ≥ 2` is CW19 Lemma 27 (PDF p.16): "Enc(x) := Enc′(x1) ◦ Enc′(x2) ◦ Enc′(x3)" with parts
"between ⌊n/3⌋ and ⌈n/3⌉", and `⌈n/3⌉ ≤ ⌊n/2⌋` for `n ≥ 2` (`ceil_third_le_floor_half`). -/
def CLW20_Lemma3_11 : Prop :=
  lemma3_11Core 2 (fun _ F => F.formulaWord)

/-- `CLW20_Lemma3_11` with one addition: the transformation also outputs the support of
every `Enc_i` (`Instance.formulaEncWord`, the import's `pcppOutput` layout). The textual
basis is CLW20 PDF p.28 ("Recall that Enc : {0, 1}^ℓ → {0, 1}^|Y| is the fixed F2-linear error
correcting code used in Lemma 3.11") and PDF p.29 (printed p.28) ("Enc_s(x) depends on at most ℓ/2 bits (the moreover part
of Lemma 3.11). We can then enumerate all these bits") and CW19 Lemma 27, PDF p.16 ("an
efficient encoder Enc"). -/
def CLW20_Lemma3_11_explicitEnc : Prop :=
  lemma3_11Core 2 (fun _ F => F.formulaEncWord)

/-! ## (b) The printed statement is false at `n = 1` -/

/-- `D(x) = x₁`: the one-input circuit whose only node reads input `0`. -/
def firstInput : BooleanCircuit 1 where
  nodes := [BooleanNode.input 0]
  output := ⟨0, by simp⟩
  wellFormed := by
    intro i
    fin_cases i
    exact trivial

theorem firstInput_eval (x : BitInput 1) : firstInput.eval x = x 0 := rfl

theorem firstInput_size : firstInput.size = 1 := rfl

/-- `D(x) = x₁` as a circuit on `n = 1` inputs of size `m = 1 ≥ n`. -/
def firstInputCircuit : CircuitFrom 1 :=
  ⟨⟨1, firstInput, by rw [firstInput_size]⟩, le_rfl⟩

/-- At `n = 1` a support of at most `⌊1/2⌋ = 0` bits is empty, so `Enc` is constant. -/
theorem enc_const_of_card_le {F : Instance 1} (h : ∀ i, (F.encSupport i).card ≤ 1 / 2)
    (x y : BitInput 1) : F.enc x = F.enc y := by
  funext i
  have hi : (F.encSupport i).card ≤ 0 := h i
  have hempty : F.encSupport i = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hi)
  simp [Instance.enc, hempty, parityOn]

/-- For every output format, the literal on circuits with `n ≥ 1` inputs is false. -/
theorem lemma3_11Core_false_at_one (outputWord : (n : ℕ) → Instance n → List Bool) :
    ¬ lemma3_11Core 1 outputWord := by
  rintro ⟨s, c, _, hsc, _, F, _, _, _, Zx, hcomplete, _, hsound, hsupport⟩
  have henc : ∀ x y : BitInput 1, (F firstInputCircuit).enc x = (F firstInputCircuit).enc y :=
    enc_const_of_card_le (hsupport firstInputCircuit)
  have hfrac : ∀ (x y : BitInput 1) (z : BitInput (F firstInputCircuit).Zbits),
      (F firstInputCircuit).fraction x z = (F firstInputCircuit).fraction y z := by
    intro x y z
    unfold Instance.fraction Instance.restrict
    rw [henc x y]
  have h1 := hcomplete firstInputCircuit (fun _ => true) (firstInput_eval _)
  have h0 := hsound firstInputCircuit (fun _ => false) (firstInput_eval _)
    (Zx firstInputCircuit fun _ => true)
  have hcs : c ≤ s :=
    calc c ≤ (F firstInputCircuit).fraction (fun _ => true)
          (Zx firstInputCircuit fun _ => true) := h1
      _ = (F firstInputCircuit).fraction (fun _ => false)
          (Zx firstInputCircuit fun _ => true) := hfrac _ _ _
      _ ≤ s := h0
  linarith

/-- **(b)** CLW20 Lemma 3.11 as printed is false (at `n = 1`, `D(x) = x₁`). -/
theorem clw20_lemma3_11_asPrinted_false : ¬ CLW20_Lemma3_11_asPrinted :=
  lemma3_11Core_false_at_one _

/-- The explicit-Enc reading is also false at `n = 1`: the counterexample does not use the
output format. -/
theorem clw20_lemma3_11_explicitEnc_false_at_one :
    ¬ lemma3_11Core 1 (fun _ F => F.formulaEncWord) :=
  lemma3_11Core_false_at_one _

/-- CW19 Lemma 27's split supports `n ≥ 2`: a third, rounded up, is at most a half, rounded
down, for every `n ≥ 2` (and `n = 0`). At `n = 1` it fails (`1 > 0`). -/
theorem ceil_third_le_floor_half (n : ℕ) : (n + 2) / 3 ≤ n / 2 ↔ 2 ≤ n ∨ n = 0 := by
  omega

/-! ## Ordinary runs: the output is no longer than the budget -/

theorem writeTapeBit_length (tape : List Bool) (position : ℕ) (value : Bool) :
    (writeTapeBit tape position value).length = max tape.length (position + 1) := by
  induction position generalizing tape with
  | zero => cases tape <;> simp [writeTapeBit]
  | succ position ih =>
    cases tape <;> simp only [writeTapeBit, List.length_cons, List.length_nil, ih]
    all_goals omega

theorem step_tape_le {t s : ℕ} (p : Machine t s) (c d : Configuration t s)
    (hs : step p c = some d) (i : Fin t) :
    (d.tapes i).length ≤ max (c.tapes i).length (c.heads i + 1) ∧
      d.heads i ≤ c.heads i + 1 := by
  unfold step at hs
  obtain ⟨action, _, he⟩ := Option.map_eq_some_iff.mp hs
  subst d
  constructor
  · simp only [applyAction]
    cases action.write i
    · exact le_max_left _ _
    · simp only [writeTapeBit_length]
      exact le_rfl
  · simp only [applyAction]
    cases action.move i <;> simp only [HeadMove.apply] <;> omega

theorem runFrom_tape_le {t s : ℕ} (p : Machine t s) (fuel : ℕ) (c : Configuration t s)
    (r : ExecutionReceipt t s) (hr : runFrom p fuel c = some r) (i : Fin t) :
    (r.final.tapes i).length ≤ max (c.tapes i).length (c.heads i + r.steps) ∧
      r.steps ≤ fuel := by
  induction fuel generalizing c r with
  | zero =>
    simp only [runFrom] at hr
    split at hr
    · cases hr
      simp
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hr
    split at hr
    · cases hr
      simp
    · cases hs : step p c with
      | none => simp [hs] at hr
      | some d =>
        cases ht : runFrom p fuel d with
        | none => simp [hs, ht] at hr
        | some tail =>
          simp only [hs, ht, Option.some.injEq] at hr
          subst r
          obtain ⟨h1, h2⟩ := ih d tail ht
          obtain ⟨h3, h4⟩ := step_tape_le p c d hs i
          dsimp only
          constructor <;> omega

/-- The output word of an ordinary word function is no longer than its budget: the output tape
starts empty, and each step grows it by at most one cell. -/
theorem output_length_le_budget {Request : Type} {input output : Request → List Bool}
    {budget : Request → ℕ} (W : OrdinaryWordFunction Request input output budget)
    (request : Request) : (output request).length ≤ budget request := by
  obtain ⟨receipt, hrun, hout⟩ := W.realizes request
  obtain ⟨hlen, hsteps⟩ := runFrom_tape_le W.program.machine (budget request) _ receipt hrun
    W.program.outputTape
  rw [hout] at hlen
  have hfresh : W.program.outputTape.val ≠ 0 := W.program.outputFresh
  have h0 : ((initialConfiguration W.program.machine
      (W.program.inputTapes (input request))).tapes W.program.outputTape).length = 0 := by
    simp [initialConfiguration, RepairOrdinary.Program.inputTapes, hfresh]
  have h1 : (initialConfiguration W.program.machine
      (W.program.inputTapes (input request))).heads W.program.outputTape = 0 := rfl
  rw [h0, h1] at hlen
  omega

/-! ## Word lengths -/

theorem natWord_length_pos (v : ℕ) : 1 ≤ (natWord v).length := by
  simp only [natWord, WilliamsPublishedForm.framedNatBits, List.length_append,
    List.length_replicate, List.length_cons]
  omega

theorem length_le_flatMap_natWord (xs : List ℕ) : xs.length ≤ (xs.flatMap natWord).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := natWord_length_pos x
    omega

theorem length_le_natListWord (xs : List ℕ) : xs.length ≤ (natListWord xs).length := by
  unfold natListWord
  rw [List.length_append]
  have := length_le_flatMap_natWord xs
  omega

theorem pairs_length {k : ℕ} (a b : Fin (2 ^ k) → ℕ) :
    ((List.ofFn fun i : Fin (2 ^ k) => [a i, b i]).flatten).length = 2 ^ k * 2 := by
  simp [List.length_flatten, List.sum_ofFn]

/-- The explicit-Enc word lists `2 · 2^clauseBits` numbers, so it has at least `2^clauseBits`
bits. -/
theorem two_pow_le_formulaEncWord_length {n : ℕ} (F : Instance n) :
    2 ^ F.clauseBits ≤ F.formulaEncWord.length := by
  unfold Instance.formulaEncWord
  simp only [List.length_append]
  have h := length_le_natListWord ((List.ofFn fun i : Fin (2 ^ F.clauseBits) =>
      [literalIndex (F.clauses i).left, literalIndex (F.clauses i).right]).flatten)
  rw [pairs_length] at h
  omega

/-! ## (d) The adapter: explicit-Enc literal → import -/

/-- An import request is a circuit with at least two inputs. -/
def toCircuit (r : PCPPRequest 2) : CircuitFrom 2 :=
  ⟨⟨r.arity, r.circuit, r.sizeLarge⟩, r.large⟩

/-- The paper objects as the import's record. The `constructionSteps` and `honestSteps` fields
carry no content in the import (its budgets are the machines' own), so they are `0`. -/
noncomputable def toPointwise {n : ℕ} {circuit : BooleanCircuit n} (F : Instance n)
    (Zx : BitInput n → BitInput F.Zbits) (h : ∀ i, (F.encSupport i).card ≤ n / 2) :
    PointwisePCPP circuit where
  systematicBits := F.Ybits
  auxiliaryBits := F.Zbits
  clauseBits := F.clauseBits
  systematicSupport := F.encSupport
  systematicSupportBound := h
  clauses := F.clauses
  honestAuxiliary := Zx
  constructionSteps := 0
  honestSteps := fun _ => 0

theorem coeff_pow_le {a b d D : ℕ} (x : ℕ) (hab : a ≤ b) (hdD : d ≤ D) :
    a * (x + 1) ^ d ≤ b * (x + 1) ^ D :=
  Nat.mul_le_mul hab (Nat.pow_le_pow_right (Nat.succ_pos x) hdD)

/-- `m + n + 1 ≤ 2 (m + 1)` because `n ≤ m`. -/
theorem budget_to_size {K e m n : ℕ} (hnm : n ≤ m) :
    K * (m + n + 1) ^ e ≤ K * 2 ^ e * (m + 1) ^ e := by
  rw [Nat.mul_assoc, ← Nat.mul_pow]
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  omega

/-- **(d)** The explicit-Enc literal gives the imported two-query PCPP source. -/
theorem clw20_lemma3_11_explicitEnc_to_import :
    CLW20_Lemma3_11_explicitEnc → PointwisePCPPSource := by
  rintro ⟨s, c, hs, hsc, hc1, F, ⟨K0, e0, ⟨W0⟩⟩, ⟨Ky, ey, hY⟩, ⟨Kz, ez, hZ⟩, Zx, hcomplete,
    ⟨Kh, eh, ⟨H⟩⟩, hsound, hsupport⟩
  -- The one place the explicit-Enc output word is used: the transformation lists Enc's supports.
  have W : OrdinaryWordFunction (CircuitFrom 2) (fun C => C.1.word)
      (fun C => (F C).formulaEncWord) (fun C => K0 * (C.1.m + C.1.n + 1) ^ e0) := W0
  let K := Ky + Kz + K0 * 2 ^ e0 + K0 + Kh + 1
  let E := ey + ez + e0 + eh
  let output : (r : PCPPRequest 2) → PointwisePCPP r.circuit := fun r =>
    toPointwise (F (toCircuit r)) (Zx (toCircuit r)) (hsupport (toCircuit r))
  have hclauses : ∀ C : CircuitFrom 2, 2 ^ (F C).clauseBits ≤ K * (C.1.m + 1) ^ E := by
    intro C
    have h1 := two_pow_le_formulaEncWord_length (F C)
    have h2 := output_length_le_budget W C
    have h3 : K0 * (C.1.m + C.1.n + 1) ^ e0 ≤ (K0 * 2 ^ e0) * (C.1.m + 1) ^ e0 :=
      budget_to_size C.1.sizeAtLeast
    have h4 : (K0 * 2 ^ e0 + 1) * (C.1.m + 1) ^ e0 ≤ K * (C.1.m + 1) ^ E :=
      coeff_pow_le _ (by omega) (by omega)
    have h5 : (K0 * 2 ^ e0) * (C.1.m + 1) ^ e0 ≤ (K0 * 2 ^ e0 + 1) * (C.1.m + 1) ^ e0 :=
      Nat.mul_le_mul_right _ (Nat.le_succ _)
    exact h1.trans (h2.trans (h3.trans (h5.trans h4)))
  let constructor0 : OrdinaryWordFunction (PCPPRequest 2) pcppInput
      (fun r => pcppOutput r (output r))
      (fun r => K0 * (r.circuit.size + r.arity + 1) ^ e0) :=
    { program := W.program
      realizes := fun r => W.realizes (toCircuit r) }
  let honest0 : OrdinaryWordFunction (Σ r : PCPPRequest 2, BitInput r.arity)
      (fun r => pcppInput r.1 ++ List.ofFn r.2)
      (fun r => List.ofFn ((output r.1).honestAuxiliary r.2))
      (fun r => Kh * (r.1.circuit.size + 1) ^ eh) :=
    { program := H.program
      realizes := fun r => H.realizes ⟨toCircuit r.1, r.2⟩ }
  refine ⟨{
    minimumArity := 2
    minimumArityBound := le_rfl
    completeness := c
    soundness := s
    soundnessPositive := hs
    gap := hsc
    completenessBelowOne := hc1
    coefficient := K
    degree := E
    coefficientPositive := by omega
    output := output
    systematicBound := fun r => (hY (toCircuit r)).trans (coeff_pow_le _ (by omega) (by omega))
    auxiliaryBound := fun r => (hZ (toCircuit r)).trans (coeff_pow_le _ (by omega) (by omega))
    clauseCountBound := fun r => hclauses (toCircuit r)
    constructor := RepairOrdinary.WordFunction.enlargeBudget constructor0
      (fun r => coeff_pow_le _ (by omega) (by omega))
    honest := RepairOrdinary.WordFunction.enlargeBudget honest0 (fun r =>
      (coeff_pow_le _ (by omega) (by omega)).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)))
    complete := fun r x hx => hcomplete (toCircuit r) x hx
    sound := fun r x hx z => hsound (toCircuit r) x hx z }⟩

end NearCubicWires.Bindings.CLW20Lemma311
