import NineInputs

/-! # The main statement is not trivially true or trivially false, and what it asserts

A check of `MainStatement`/`MainAt` in the trusted statement against the main theorem
(`thm:main`) and the reading of "almost everywhere" fixed before it
(`sec:intro`, "Main theorem, informally"); `SourceMapping/main-theorem.md` (item 1) compares the quantifiers.

A skeptic should check that the conclusion cannot hold for a degenerate reason (an empty range of circuits,
an agreement measure that never reaches the bound), that it cannot fail for a degenerate reason (an
`E^NP` predicate no language satisfies, which would make the main statement false and the implication
`NineFinalStatement` vacuous), and what the existential constant `γ` contributes. This module proves:

* `constantCircuit_mainBudget`: the constant circuit (no bottom gates) lies within every budget, so the
  conclusion always quantifies over at least one circuit.
* `constant_language_fails`: a constant language violates the conclusion at every length, for every `K`
  and every `d > 0`; the conclusion has teeth.
* `constantFalse_inENP`: the `E^NP` predicate `InENP` is satisfiable, by the constant language with an
  explicit two-state program and an explicit verifier for the empty NP oracle.
* `mainStatement_iff_exists_d`: `MainStatement` is equivalent to constant-error hardness for one constant
  `d > 0`. As in the paper, `γ` is existential, so the window `0 < d < γ/5` carries no further content;
  the paper's remark that `γ` comes from a published PCPP (the remark after `thm:main`) is not part of the
  theorem.
-/

namespace NearCubicGates.StatementChecks.Nontrivial

open NearCubicGates.Target NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairSource

set_option autoImplicit false

/-! ## The conclusion has teeth -/

/-- The circuit with no bottom gates and a constant lookup. -/
def constantCircuit (n : ℕ) (value : Bool) : WeightedSymmetricCircuit n where
  bottomCount := 0
  bottom := Fin.elim0
  coefficient := Fin.elim0
  coefficient_ne_zero := fun i => Fin.elim0 i
  lookup := fun _ => value

/-- The constant circuit has top weight zero and so lies within every budget. -/
theorem constantCircuit_mainBudget (K n : ℕ) (value : Bool) :
    MainBudget K n (constantCircuit n value).topWeight := by
  simp [MainBudget, WeightedSymmetricCircuit.topWeight, constantCircuit]

/-- For a constant language, the conclusion of `MainAt` fails at every length, for every `K` and `d > 0`. -/
theorem constant_language_fails (K n : ℕ) (d : ℝ) (hd : 0 < d) (value : Bool) :
    ¬ ∀ C : WeightedSymmetricCircuit n, MainBudget K n C.topWeight →
        agreement C (fun _ _ => value) < 1 - d := by
  intro h
  have hlt := h (constantCircuit n value) (constantCircuit_mainBudget K n value)
  have h1 : agreement (constantCircuit n value) (fun _ _ => value) = 1 := by
    simp [agreement, WeightedSymmetricCircuit.eval, constantCircuit]
  linarith

/-! ## `InENP` is satisfiable -/

/-- A verifier that halts at once and never accepts. -/
def rejectingVerifier : RepairOrdinary.Verifier where
  tapeCount := 2
  stateCount := 1
  twoTapes := le_refl 2
  machine := { descriptionBits := 0, start := 0, halted := fun _ => true, rule := fun _ _ => none }
  accepting := fun _ => false

/-- The empty oracle has an NP verifier. -/
def emptyOracleVerifier : EncodedNPVerifier (fun _ => false) where
  verifier := rejectingVerifier
  coefficient := 1
  coefficientPositive := le_refl 1
  degree := 0
  correct := by
    intro code
    simp [RepairOrdinary.Verifier.acceptsAt, rejectingVerifier]

/-- The one action of the program: write `false` on the output tape and halt. -/
def writeFalseAction : Action 2 2 :=
  { nextControl := 1, write := fun t => if t.val = 1 then some false else none, move := fun _ => .stay }

/-- A two-tape, two-state machine that writes the framed empty word on tape 1 and halts. -/
def writeFalseMachine : Machine 2 2 where
  descriptionBits := 0
  start := 0
  halted := fun i => decide (i.val = 1)
  rule := fun i _ => if i.val = 0 then some writeFalseAction else none

/-- The oracle program running `writeFalseMachine`; it never queries the oracle. -/
def constantFalseProgram : OrdinaryOracleProgram where
  base := { tapeCount := 2, stateCount := 2, twoTapes := le_refl 2, machine := writeFalseMachine,
            outputTape := 1, outputFresh := by decide }
  queryTape := (1 : Fin 2)
  queryFresh := by decide
  query := fun _ => none

/-- The program computes the constant-false language in one step, within the budget `2^(max 1 n)`. -/
def constantFalseCertificate : OrdinaryENPCertificate (fun _ => false) (fun _ _ => false) where
  program := constantFalseProgram
  exponent := 1
  exponentPositive := le_refl 1
  computes := by
    intro n input
    let init := initialConfiguration constantFalseProgram.base.machine
      (constantFalseProgram.base.inputTapes (List.ofFn input))
    refine ⟨1 + 0, applyAction init writeFalseAction, ?_, ?_, ?_, ?_⟩
    · have h : (1 : ℕ) ≤ 2 ^ (1 * max 1 n) := Nat.one_le_two_pow
      simpa using h
    · exact OrdinaryOracleTrace.cons (OrdinaryOracleStep.local init _ rfl rfl rfl)
        (OrdinaryOracleTrace.refl _)
    · rfl
    · simp [applyAction, writeFalseAction, init, initialConfiguration, constantFalseProgram,
        RepairOrdinary.Program.inputTapes, writeTapeBit, RepairOrdinary.frame]

/-- The constant-false language is in `E^NP` in the sense of the trusted statement. -/
theorem constantFalse_inENP : InENP (fun _ _ => false) :=
  ⟨_, ⟨emptyOracleVerifier⟩, ⟨constantFalseCertificate⟩⟩

/-! ## What `MainStatement` asserts -/

/-- `MainStatement` holds exactly when one constant `d > 0` has a positive `K`, an `E^NP` language and
an onset beyond which every circuit within the budget agrees with the language on less than `1 - d` of
inputs. -/
theorem mainStatement_iff_exists_d :
    MainStatement ↔ ∃ d : ℝ, 0 < d ∧ ∃ K : ℕ, 0 < K ∧ ∃ F : Language, InENP F ∧
      ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∀ C : WeightedSymmetricCircuit n,
        MainBudget K n C.topWeight → agreement C F < 1 - d := by
  constructor
  · rintro ⟨γ, hγ0, _, h⟩
    have hγ : (0 : ℝ) < γ := by exact_mod_cast hγ0
    exact ⟨(γ : ℝ) / 10, by positivity, h _ (by positivity) (by linarith)⟩
  · rintro ⟨d₀, hd₀, K, hK, F, hF, n₀, hn₀, h⟩
    obtain ⟨q, hq0, hq⟩ := exists_rat_btwn (show (0 : ℝ) < min 1 (5 * d₀) by positivity)
    refine ⟨q, by exact_mod_cast hq0, ?_, ?_⟩
    · have hq1 : (q : ℝ) < 1 := lt_of_lt_of_le hq (min_le_left _ _)
      exact_mod_cast hq1
    · intro d _ hdq
      refine ⟨K, hK, F, hF, n₀, hn₀, fun n hn C hC => ?_⟩
      have h5 : (q : ℝ) ≤ 5 * d₀ := le_of_lt (lt_of_lt_of_le hq (min_le_right _ _))
      have hlt := h n hn C hC
      linarith

end NearCubicGates.StatementChecks.Nontrivial
