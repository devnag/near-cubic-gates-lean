import Proof.Foundations.RecoverySourceContracts
import StatementSupport

/-!
# Binding: CLW20 Lemma 3.9 (from [STV01]) → `Nonempty RepairSource.SourceAmplifierFactory`

Source PDF: `CLW20_Chen_Lyu_Williams_AE_Circuit_Lower_Bounds_ECCC_TR20-150.pdf`.

* PDF page 18 (printed p.17), §3.4, verbatim:
  "Lemma 3.9 ([STV01]). There is a constant c ≥ 1 such that, for any time-constructible function
  S(n) and every f : {0, 1}^n → {0, 1} that does not have (general) circuits of size S(n). There is
  a function g : {0, 1}^{O(n)} → {0, 1} that cannot be (1/2 + S(n)^{−1/c})-approximated by
  circuits of size S(n)^{1/c}. Furthermore, given the 2^n-length truth table of f, the truth table
  of g can be constructed in 2^{O(n)} time."
* PDF page 3 (printed p.2), the paper's own definition of approximation, verbatim:
  "We say that a function f : {0, 1}^n → {0, 1} cannot be (1/2 + ε)-approximated by circuits of
  type C, if every circuit from C computes f correctly on less than (1/2 + ε)2^n of the n-bit
  inputs."
* PDF page 17 (printed p.16), Lemma 3.6, the paper's reading of "circuits of size s", verbatim:
  "(general) circuits of size s. That is, for all circuit C of size at most s".
* The cited source is STV01 (`stv-2001.pdf`), Theorem 24, PDF p.20 (printed p.255):
  "Then no circuit of size s′ = (ε/l)^c · s computes the predicate C_{2^l,ε}(P) correctly on more
  than a 1/2 + ε fraction of the inputs." and PDF p.21: "Moreover, P′ can be evaluated in time
  2^{O(l)} with access to the entire truth table of P." (Lemma 28, PDF pp.22–23, supplies the
  nice binary codes.)

## Transcription choices

* **Quantifier order, as printed.** `∃ c ≥ 1` comes FIRST: one `c` for every `S`. Then `∀ S`
  time-constructible. Everything the sentence hides after that may depend on `S` (weakest
  reading): the function family `g`, the constant and onset of `O(n)`, the construction
  algorithm, and the constant and onset of `2^{O(n)}`. Then `∀ n`, `∀ f`.
* **`c` is a REAL constant `c ≥ 1`**, as printed ("a constant c ≥ 1"); the adapter rounds it up.
* **Time-constructible** is the repo's `SourceInterfaces.TimeConstructible` (a sat-free register
  program returning `S n` from `n` within `K·(S n + 1)` steps and `K·(S n + 1)` register bits).
  CLW20 uses the standard notion (a machine outputs `S(n)` in `O(S(n))` time) without defining
  it. The two agree up to polynomial overhead: a multitape run of `O(S)` steps is simulated by
  `O(S)` register steps of width `O(S)`, and such a register run is simulated in `poly(S)`
  multitape time. The repo class may therefore be slightly LARGER, which makes this literal
  slightly stronger than the printed one; that cannot make it
  false, because the lemma uses constructibility only so that its algorithm can learn `S(n)`.
  Values of `S(n)` above the size of a truth-table circuit make the hypothesis empty, so the
  algorithm only needs `min(S(n), 2^{O(n)})`, which a resource-capped run of the register program
  yields (runs are monotone in fuel and width) in `2^{O(n)}` multitape time. The adapter
  instantiates it only at the fixed schedule `oracleSizeBound d`, through
  `oracleSizeBoundConstructible d`.
* **Circuits and size.** CLW20 defines neither and defers to its textbooks ("We assume knowledge
  of basic complexity theory (see [AB09, Gol08] for excellent references)", PDF p.15). The literal
  uses the repo's `BooleanCircuit` (fan-in-two De Morgan DAG with constant nodes), whose `size` is
  the NODE count, input nodes included (the vertex-count convention of Arora–Barak). A gate-count
  convention differs by at most the `n` input nodes and two constants. For large `S` the one constant
  `c` absorbs that; for small `S` the node count is what makes the parity argument work (a circuit
  with fewer than `m` nodes cannot read all `m` inputs, `parity_small_circuit` in the support
  module). "circuits of size s" = size at most s (Lemma 3.6 above).
* **"does not have circuits of size S(n)"** = no circuit of size at most `S n` computes `f` on
  every input (`HasCircuitOfSize`).
* **"cannot be (1/2 + ε)-approximated by circuits of size s"** follows the p.3 definition literally:
  every circuit of size at most `s` is correct on STRICTLY LESS than `(1/2 + ε)·2^m` of the `m`-bit
  inputs (`CannotBeApproximated`). This is stronger than the import's `≤`. It is still implied by
  STV's "more than" form at any smaller exponent (`strict_of_nonstrict` in the support module).
* **Sizes and exponents are real**: `S(n)^{1/c}` and `S(n)^{−1/c}` are `Real.rpow`. The import's
  `integerFloorRoot` is bridged by `le_integerFloorRoot_iff`.
* **"g : {0,1}^{O(n)} → {0,1}"**: one constant `arityFactor` and one onset `arityOnset`, uniform in
  `f`, with arity `≤ arityFactor·n` for `n ≥ arityOnset`, stated for the hard `f` the sentence
  speaks about. The adapter does not use this clause: the import's arity bound for EVERY `f` is
  derived from the time bound, since the machine writes the full table of `g` on a fresh tape.
* **The algorithm is total.** "given the 2^n-length truth table of f, the truth table of g can be
  constructed" is one algorithm whose input is an arbitrary truth table; hardness of `f` is not an
  input and cannot be decided within `2^{O(n)}` time. STV's source (Theorem 24, `P′ = C_{2^l,ε}(P)`
  for every `P`, evaluated "with access to the entire truth table of P") is total in the same way.
  So `g n f` is the algorithm's output for every `f`, and hardness is claimed for hard `f` only.
* **"2^{O(n)} time"**: a constant `timeExponent` and an onset `timeOnset`; the budget is at most
  `2^(timeExponent·n)` for `n ≥ timeOnset`, and is otherwise unconstrained (weakest reading).
* **Tier 1 machine model.** The algorithmic clause is the separable structure
  `TruthTableConstruction`, stated in the repo's model `RepairOrdinary.WordFunction`
  (`OrdinaryWordFunction`, `Proof/Foundations/OrdinaryMachine.lean`). Its input word is the import's
  `amplifierInput` (framed arity, then the full truth table of `f`) and its output word is the
  framed arity of `g` followed by the full truth table of `g`. Tier 2 replaces only this structure.
-/

namespace NearCubicWires.Bindings.CLW20Lemma39

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.LocalBitMultitape
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option warningAsError true
set_option maxRecDepth 120000

/-! ## The literal -/

/-- The word the algorithm writes: the framed arity of `g`, then the full truth table of `g`. -/
def truthTableWord (g : (n : ℕ) → BoolFunction n → AmplifierOutput)
    (request : AmplifierRequest) : List Bool :=
  RepairOrdinary.frame (g request.inputArity request.function).arity.bits ++
    boolFunctionTable (g request.inputArity request.function).function

/-- TIER 1 ALGORITHMIC CLAUSE (separable). "given the 2^n-length truth table of f, the truth
table of g can be constructed in 2^{O(n)} time": one ordinary multitape program, run on every
request, with a budget that is at most `2^(timeExponent·n)` from the onset `timeOnset` on. -/
structure TruthTableConstruction (g : (n : ℕ) → BoolFunction n → AmplifierOutput) where
  budget : AmplifierRequest → ℕ
  algorithm : OrdinaryWordFunction AmplifierRequest amplifierInput (truthTableWord g) budget
  timeExponent : ℕ
  timeOnset : ℕ
  exponentialTime : ∀ request : AmplifierRequest, timeOnset ≤ request.inputArity →
    budget request ≤ 2 ^ (timeExponent * request.inputArity)

/-- What the sentence asserts for one constant `c` and one time-constructible `S`. -/
structure Lemma3_9At (c : ℝ) (S : ℕ → ℕ) where
  /-- `g` for the input `f` on `n` bits. -/
  g : (n : ℕ) → BoolFunction n → AmplifierOutput
  /-- The hidden constant of `O(n)`. -/
  arityFactor : ℕ
  /-- The hidden onset of `O(n)`. -/
  arityOnset : ℕ
  /-- "every f ... that does not have (general) circuits of size S(n). There is a function
  g : {0,1}^{O(n)} → {0,1} that cannot be (1/2 + S(n)^{−1/c})-approximated by circuits of size
  S(n)^{1/c}." -/
  amplifies : ∀ (n : ℕ) (f : BoolFunction n), ¬ HasCircuitOfSize f (S n) →
    (arityOnset ≤ n → (g n f).arity ≤ arityFactor * n) ∧
    CannotBeApproximated (g n f).function
      ((S n : ℝ) ^ (-(1 : ℝ) / c)) ((S n : ℝ) ^ ((1 : ℝ) / c))
  /-- "Furthermore, given the 2^n-length truth table of f, the truth table of g can be
  constructed in 2^{O(n)} time." (Tier 1.) -/
  construction : TruthTableConstruction g

/-- **CLW20 Lemma 3.9, literal (Tier 1).** "There is a constant c ≥ 1 such that, for any
time-constructible function S(n) and every f ..." -/
def CLW20_Lemma3_9 : Prop :=
  ∃ c : ℝ, 1 ≤ c ∧ ∀ S : ℕ → ℕ, TimeConstructible S → Nonempty (Lemma3_9At c S)

/-! ## Semantic bridges -/

theorem card_bitInput (m : ℕ) : (Fintype.card (BitInput m) : ℝ) = 2 ^ m := by
  simp [BitInput]

/-- The p.3 counting form is the repo's `agreement` below `1/2 + ε`. -/
theorem count_lt_iff_agreement_lt {m : ℕ} (circuit : BooleanCircuit m) (g : BoolFunction m)
    (ε : ℝ) :
    ((Finset.univ.filter fun x => circuit.eval x = g x).card : ℝ) < (1 / 2 + ε) * 2 ^ m ↔
      agreement circuit.eval g < 1 / 2 + ε := by
  unfold agreement
  rw [card_bitInput, div_lt_iff₀ (by positivity)]

theorem not_hasCircuitOfSize {n : ℕ} {f : BoolFunction n} {s : ℕ}
    (hhard : WorstCaseHardAt f s) : ¬ HasCircuitOfSize f s := by
  rintro ⟨circuit, hsize, hcomputes⟩
  obtain ⟨x, hx⟩ := hhard circuit hsize
  exact hx (hcomputes x)

/-- The integer floor root lies below the real root at any smaller real exponent. -/
theorem natCast_le_rpow_of_pow_le {t S k : ℕ} {c : ℝ} (hc : 0 < c) (hk : 0 < k)
    (hck : c ≤ k) (hpow : t ^ k ≤ S) : (t : ℝ) ≤ (S : ℝ) ^ ((1 : ℝ) / c) := by
  rcases Nat.eq_zero_or_pos S with hS | hS
  · subst hS
    have ht : t = 0 := by
      rcases Nat.eq_zero_or_pos t with ht | ht
      · exact ht
      · have := pow_pos ht k
        omega
    subst ht
    simpa using Real.rpow_nonneg (le_refl (0 : ℝ)) ((1 : ℝ) / c)
  · have hkne : (k : ℕ) ≠ 0 := by omega
    have htk : ((t : ℝ) ^ k) ≤ (S : ℝ) := by exact_mod_cast hpow
    have hroot : (t : ℝ) = ((t : ℝ) ^ k) ^ ((k : ℝ)⁻¹) :=
      (Real.pow_rpow_inv_natCast (by positivity) hkne).symm
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hexp : (k : ℝ)⁻¹ ≤ (1 : ℝ) / c := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le hc hck
    have hS1 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
    calc (t : ℝ) = ((t : ℝ) ^ k) ^ ((k : ℝ)⁻¹) := hroot
      _ ≤ (S : ℝ) ^ ((k : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) htk (by positivity)
      _ ≤ (S : ℝ) ^ ((1 : ℝ) / c) := Real.rpow_le_rpow_of_exponent_le hS1 hexp

/-- Rounding the exponent up can only enlarge the advantage `S^(-1/c)`. -/
theorem rpow_neg_le_rpow_neg_of_le {S : ℕ} {c k : ℝ} (hc : 0 < c) (hck : c ≤ k) :
    (S : ℝ) ^ (-(1 : ℝ) / c) ≤ (S : ℝ) ^ (-(1 : ℝ) / k) := by
  rcases Nat.eq_zero_or_pos S with hS | hS
  · subst hS
    have hkpos : 0 < k := lt_of_lt_of_le hc hck
    have h1 : -(1 : ℝ) / c ≠ 0 := div_ne_zero (by norm_num) hc.ne'
    have h2 : -(1 : ℝ) / k ≠ 0 := div_ne_zero (by norm_num) hkpos.ne'
    simp [Real.zero_rpow h1, Real.zero_rpow h2]
  · have hS1 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
    apply Real.rpow_le_rpow_of_exponent_le hS1
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact one_div_le_one_div_of_le hc hck

/-! ## Machine facts: a fresh output tape is no longer than the run -/

/-- Same statement as `RecoveryTapeSupport.write_length` (`Proof/Amplification/RecoveryTapeSupport.lean`);
restated here so this module keeps the import cone of the source contract. -/
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

/-- One tape grows by at most one cell per step past its head; and a run uses at most its fuel
(the latter as `runFrom_steps_le`, `Proof/Foundations/OrdinaryRewindCarrier.lean`). -/
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

/-- The output word of an ordinary word function is no longer than its budget. -/
theorem output_length_le_budget {Request : Type} {input output : Request → List Bool}
    {budget : Request → ℕ} (F : OrdinaryWordFunction Request input output budget)
    (request : Request) : (output request).length ≤ budget request := by
  obtain ⟨receipt, hrun, hout⟩ := F.realizes request
  obtain ⟨hlen, hsteps⟩ := runFrom_tape_le F.program.machine (budget request) _ receipt hrun
    F.program.outputTape
  rw [hout] at hlen
  have hfresh : F.program.outputTape.val ≠ 0 := F.program.outputFresh
  have h0 : ((initialConfiguration F.program.machine
      (F.program.inputTapes (input request))).tapes F.program.outputTape).length = 0 := by
    simp [initialConfiguration, RepairOrdinary.Program.inputTapes, hfresh]
  have h1 : (initialConfiguration F.program.machine
      (F.program.inputTapes (input request))).heads F.program.outputTape = 0 := rfl
  rw [h0, h1] at hlen
  omega

/-! ## From an eventual `2^{O(n)}` budget to the import's uniform budget -/

/-- The total budget over the finitely many requests below the time onset. -/
def smallBudgetMass (budget : AmplifierRequest → ℕ) (onset : ℕ) : ℕ :=
  ∑ n ∈ Finset.range onset, ∑ f : BoolFunction n, budget ⟨n, f⟩

theorem budget_le_smallBudgetMass (budget : AmplifierRequest → ℕ) (onset : ℕ)
    (request : AmplifierRequest) (hsmall : request.inputArity < onset) :
    budget request ≤ smallBudgetMass budget onset := by
  obtain ⟨n, f⟩ := request
  unfold smallBudgetMass
  calc budget ⟨n, f⟩ ≤ ∑ f' : BoolFunction n, budget ⟨n, f'⟩ :=
        Finset.single_le_sum (f := fun f' : BoolFunction n => budget ⟨n, f'⟩)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ f)
    _ ≤ ∑ m ∈ Finset.range onset, ∑ f' : BoolFunction m, budget ⟨m, f'⟩ :=
        Finset.single_le_sum (f := fun m => ∑ f' : BoolFunction m, budget ⟨m, f'⟩)
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hsmall)

/-- One exponent serving every request, small ones included. -/
def uniformExponent {g : (n : ℕ) → BoolFunction n → AmplifierOutput}
    (T : TruthTableConstruction g) : ℕ :=
  T.timeExponent + smallBudgetMass T.budget T.timeOnset + 1

theorem one_le_uniformExponent {g : (n : ℕ) → BoolFunction n → AmplifierOutput}
    (T : TruthTableConstruction g) : 1 ≤ uniformExponent T := by
  unfold uniformExponent
  omega

theorem budget_le_uniform {g : (n : ℕ) → BoolFunction n → AmplifierOutput}
    (T : TruthTableConstruction g) (request : AmplifierRequest) :
    T.budget request ≤ 2 ^ (uniformExponent T * max 1 request.inputArity) := by
  have hmax : 1 ≤ max 1 request.inputArity := le_max_left _ _
  by_cases hon : T.timeOnset ≤ request.inputArity
  · have hexp : T.timeExponent * request.inputArity ≤
        uniformExponent T * max 1 request.inputArity := by
      apply Nat.mul_le_mul
      · unfold uniformExponent
        omega
      · exact le_max_right _ _
    exact (T.exponentialTime request hon).trans (Nat.pow_le_pow_right (by norm_num) hexp)
  · have hsmall := budget_le_smallBudgetMass T.budget T.timeOnset request (by omega)
    have hlt : smallBudgetMass T.budget T.timeOnset < 2 ^ smallBudgetMass T.budget T.timeOnset :=
      Nat.lt_two_pow_self
    have hexp : smallBudgetMass T.budget T.timeOnset ≤
        uniformExponent T * max 1 request.inputArity := by
      calc smallBudgetMass T.budget T.timeOnset ≤ uniformExponent T := by
            unfold uniformExponent
            omega
        _ = uniformExponent T * 1 := (Nat.mul_one _).symm
        _ ≤ uniformExponent T * max 1 request.inputArity := Nat.mul_le_mul_left _ hmax
    have hpow := Nat.pow_le_pow_right (by norm_num : 0 < 2) hexp
    omega

theorem truthTableWord_length_ge (g : (n : ℕ) → BoolFunction n → AmplifierOutput)
    (request : AmplifierRequest) :
    2 ^ (g request.inputArity request.function).arity ≤ (truthTableWord g request).length := by
  unfold truthTableWord boolFunctionTable
  simp

/-- The arity bound for EVERY `f`, read off the time bound: the full table of `g` is written. -/
theorem arity_le_uniform {g : (n : ℕ) → BoolFunction n → AmplifierOutput}
    (T : TruthTableConstruction g) (n : ℕ) (f : BoolFunction n) :
    (g n f).arity ≤ uniformExponent T * max 1 n := by
  have h1 := truthTableWord_length_ge g ⟨n, f⟩
  have h2 := output_length_le_budget T.algorithm ⟨n, f⟩
  have h3 := budget_le_uniform T ⟨n, f⟩
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp ((h1.trans h2).trans h3)

/-! ## The adapter -/

/-- The import's soundness clause from the literal's, at any hardness function `S`. -/
theorem sound_of_literal {c : ℝ} (hc : 1 ≤ c) {S : ℕ → ℕ} (W : Lemma3_9At c S) (q : ℕ)
    (f : BoolFunction q) (hhard : WorstCaseHardAt f (S q))
    (circuit : BooleanCircuit (W.g q f).arity)
    (hsize : circuit.size ≤ integerFloorRoot ⌈c⌉₊ (S q)) :
    agreement circuit.eval (W.g q f).function ≤
      1 / 2 + Real.rpow (S q : ℝ) (-(1 : ℝ) / (⌈c⌉₊ : ℕ)) := by
  have hcpos : 0 < c := by linarith
  have hk : 0 < ⌈c⌉₊ := Nat.ceil_pos.mpr hcpos
  have hck : c ≤ (⌈c⌉₊ : ℝ) := Nat.le_ceil c
  have hpow : circuit.size ^ ⌈c⌉₊ ≤ S q := (le_integerFloorRoot_iff hk).mp hsize
  have hreal : (circuit.size : ℝ) ≤ (S q : ℝ) ^ ((1 : ℝ) / c) :=
    natCast_le_rpow_of_pow_le hcpos hk hck hpow
  have hcount := (W.amplifies q f (not_hasCircuitOfSize hhard)).2 circuit hreal
  have hstrict := (count_lt_iff_agreement_lt circuit (W.g q f).function _).mp hcount
  have hadv := rpow_neg_le_rpow_neg_of_le (S := S q) hcpos hck
  change agreement circuit.eval (W.g q f).function ≤
    1 / 2 + (S q : ℝ) ^ (-(1 : ℝ) / ((⌈c⌉₊ : ℕ) : ℝ))
  linarith

/-- The scheduled amplifier the import asks for, built from the literal at `S = oracleSizeBound d`. -/
noncomputable def scheduleAmplifierOfLiteral {c : ℝ} (hc : 1 ≤ c) (d : ℕ)
    (W : Lemma3_9At c (oracleSizeBound d)) : OrdinaryScheduleAmplifier ⌈c⌉₊ d where
  arityCoefficient := uniformExponent W.construction
  arityCoefficientPositive := one_le_uniformExponent W.construction
  output := W.g
  arityBound := fun q f hq => by
    have h := arity_le_uniform W.construction q f
    rwa [max_eq_right hq] at h
  sound := fun q f _ hhard circuit hsize => sound_of_literal hc W q f hhard circuit hsize
  constructionExponent := uniformExponent W.construction
  constructionExponentPositive := one_le_uniformExponent W.construction
  constructor := W.construction.algorithm.enlargeBudget (budget_le_uniform W.construction)

/-- **A2.** The printed CLW20 Lemma 3.9 (Tier 1) implies the imported amplifier source. -/
theorem clw20_lemma3_9_to_import : CLW20_Lemma3_9 → Nonempty SourceAmplifierFactory := by
  rintro ⟨c, hc, hlit⟩
  exact ⟨{ stvExponent := ⌈c⌉₊
           stvExponentPositive := Nat.ceil_pos.mpr (by linarith)
           forSchedule := fun d =>
             (hlit (oracleSizeBound d) (oracleSizeBoundConstructible d)).map
               (scheduleAmplifierOfLiteral hc d) }⟩

end NearCubicWires.Bindings.CLW20Lemma39
