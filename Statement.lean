import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Digits.Defs

/-!
# The statement: the main theorem and the published results it assumes

This file is the whole trusted statement: `Challenge.lean` imports it, and it imports Mathlib only. It
declares the definitions that `FinalStatement` reaches. The last section states `FinalStatement`: the
published results collected in `PublishedInputs` imply `NearCubicGates.Target.MainStatement`, the paper's main
theorem (`thm:main` in `paper/paper.tex`).

The first sections are the machine and circuit models and the main theorem's statement. Each later section is
one published source: its statement transcribed in the source's own model, with the locator, the pinned copy,
the quantifier ledger, the conventions and what is not claimed. `PublishedInputs` has one field per published
statement. The proof derives the nine intermediate inputs of `main_from_inputs` (`NineInputs`, defined in the
proof module `NineInputs.lean`, which imports this file) from `PublishedInputs`; nothing outside this file
and Mathlib is trusted.

## Contents

1. Bit length of natural numbers
2. Binary codes of lists, Booleans and numbers
3. Boolean inputs and functions, real threshold gates, Boolean circuits
4. The multitape bit machine
5. Framing, programs, word functions and verifiers
6. Ordinary programs, word functions, verifiers, hierarchies and weak machines; projection and literal codes
7. Oracle programs, NP verifiers and E^NP certificates
8. The main theorem's statement (`thm:main`): `MainStatement`
9. Relative Hamming distance
10. Published statement: the prime number theorem as stated in Apostol, p. 74
11. BCGT13: the strong PCPP verifiers `V_RS`, `V_VRS` and their soundness (published statements)
12. CW19 Lemma 26: the source linear code
13. Published statements: CW19Proximity
14. Published statement: STV Theorem 29 (list decoding of multivariate polynomials)
15. FindIrrPoly: deterministic polynomial-time irreducible polynomials over `F2` (published statement)
16. Published statement: Williams, JACM 2014, Corollary 4.4 (= Corollary C.2), in the multitape model
17. The published inputs and the final statement: `PublishedInputs`, `FinalStatement`
-/

/-! ## 1. Bit length of natural numbers -/

section

namespace NearCubicWires

def natBitLength (value : ℕ) : ℕ := Nat.log 2 value + 1

end NearCubicWires
end

/-! ## 2. Binary codes of lists, Booleans and numbers -/

section

namespace NearCubicWires.CanonicalBinary

open NearCubicWires

def bitsValue : List Bool → ℕ
  | [] => 0
  | bit :: rest => bit.toNat + 2 * bitsValue rest

end NearCubicWires.CanonicalBinary
end

/-! ## 3. Boolean inputs and functions, real threshold gates, Boolean circuits -/

section

open Finset
open scoped BigOperators

namespace NearCubicWires

abbrev BitInput (n : ℕ) := Fin n → Bool

abbrev BoolFunction (n : ℕ) := BitInput n → Bool

abbrev Language := (n : ℕ) → BoolFunction n

def bitAsReal (bit : Bool) : ℝ := if bit then 1 else 0

/-- A semantic threshold gate together with its exact retained support. -/
structure RealThresholdGate (n : ℕ) where
  weight : Fin n → ℝ
  threshold : ℝ
  support : Finset (Fin n)
  mem_support_iff : ∀ i, i ∈ support ↔ weight i ≠ 0

noncomputable def RealThresholdGate.eval {n : ℕ} (gate : RealThresholdGate n)
    (input : BitInput n) : Bool :=
  decide (gate.threshold ≤ ∑ i, gate.weight i * bitAsReal (input i))

/-- One node in a topologically ordered fan-in-two Boolean DAG.  Child
references are natural-number node addresses; `BooleanCircuit.wellFormed`
requires every child to precede the node that uses it. -/
inductive BooleanNode (n : ℕ) where
  | const (value : Bool)
  | input (index : Fin n)
  | not (child : ℕ)
  | and (left right : ℕ)
  | or (left right : ℕ)
  deriving Repr

def BooleanNode.WellFormedAt {n : ℕ} (index : ℕ) :
    BooleanNode n → Prop
  | .const _ => True
  | .input _ => True
  | .not child => child < index
  | .and left right => left < index ∧ right < index
  | .or left right => left < index ∧ right < index

def BooleanNode.eval {n : ℕ} (input : BitInput n)
    (prior : Array Bool) : BooleanNode n → Bool
  | .const value => value
  | .input index => input index
  | .not child => !(prior[child]?.getD false)
  | .and left right =>
      prior[left]?.getD false && prior[right]?.getD false
  | .or left right =>
      prior[left]?.getD false || prior[right]?.getD false

/-- General Boolean circuits (fan-in-two AND and OR, NOT, constants and inputs): finite DAGs with a topological
node order. Their size counts DAG nodes, so a shared subcircuit counts once (it is not the size of the unfolded
formula); see `BooleanCircuit.size`. -/
structure BooleanCircuit (n : ℕ) where
  nodes : List (BooleanNode n)
  output : Fin nodes.length
  wellFormed :
    ∀ index : Fin nodes.length,
      (nodes.get index).WellFormedAt index.val
  deriving Repr

def BooleanCircuit.values {n : ℕ} (circuit : BooleanCircuit n)
    (input : BitInput n) : Array Bool :=
  circuit.nodes.foldl
    (fun prior node => prior.push (node.eval input prior)) #[]

def BooleanCircuit.eval {n : ℕ} (circuit : BooleanCircuit n)
    (input : BitInput n) : Bool :=
  (circuit.values input)[circuit.output.val]?.getD false

/-- The number of nodes, input and constant nodes included (the circuit's vertex count). -/
def BooleanCircuit.size {n : ℕ} (circuit : BooleanCircuit n) : ℕ :=
  circuit.nodes.length

end NearCubicWires
end

/-! ## 4. The multitape bit machine -/

section

namespace NearCubicWires.LocalBitMultitape

inductive HeadMove where
  | left
  | stay
  | right
deriving DecidableEq

def HeadMove.apply (move : HeadMove) (head : ℕ) : ℕ :=
  match move with
  | .left => head - 1
  | .stay => head
  | .right => head + 1

def readTapeBit (tape : List Bool) (position : ℕ) : Bool :=
  tape.getD position false

/-- Write one cell, extending a one-sided tape with blank (`false`) cells when
the head is just beyond its currently materialized support. -/
def writeTapeBit : List Bool → ℕ → Bool → List Bool
  | [], 0, value => [value]
  | [], position + 1, value => false :: writeTapeBit [] position value
  | _old :: tail, 0, value => value :: tail
  | old :: tail, position + 1, value =>
      old :: writeTapeBit tail position value

structure Configuration (tapeCount stateCount : ℕ) where
  control : Fin stateCount
  heads : Fin tapeCount → ℕ
  tapes : Fin tapeCount → List Bool

def Configuration.tapeCells
    {tapeCount stateCount : ℕ}
    (configuration : Configuration tapeCount stateCount) : ℕ :=
  ∑ tape : Fin tapeCount, (configuration.tapes tape).length

def Configuration.scanned
    {tapeCount stateCount : ℕ}
    (configuration : Configuration tapeCount stateCount) :
    Fin tapeCount → Bool :=
  fun tape => readTapeBit (configuration.tapes tape)
    (configuration.heads tape)

/-- A finite local action: one replacement bit and one unit head move per
tape, plus the next finite control state. -/
structure Action (tapeCount stateCount : ℕ) where
  nextControl : Fin stateCount
  /-- `none` leaves a tape unchanged; `some bit` writes exactly its scanned
  cell. -/
  write : Fin tapeCount → Option Bool
  move : Fin tapeCount → HeadMove

/-- The transition function has a finite domain (`Fin stateCount` and one bit
per tape), so it is extensionally a finite transition table. -/
structure Machine (tapeCount stateCount : ℕ) where
  descriptionBits : ℕ
  start : Fin stateCount
  halted : Fin stateCount → Bool
  rule : Fin stateCount → (Fin tapeCount → Bool) →
    Option (Action tapeCount stateCount)

def applyAction
    {tapeCount stateCount : ℕ}
    (configuration : Configuration tapeCount stateCount)
    (action : Action tapeCount stateCount) :
    Configuration tapeCount stateCount where
  control := action.nextControl
  heads := fun tape => (action.move tape).apply (configuration.heads tape)
  tapes := fun tape =>
    match action.write tape with
    | none => configuration.tapes tape
    | some value =>
        writeTapeBit (configuration.tapes tape) (configuration.heads tape) value

def step
    {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount)
    (configuration : Configuration tapeCount stateCount) :
    Option (Configuration tapeCount stateCount) :=
  (machine.rule configuration.control configuration.scanned).map
    (applyAction configuration)

/-- Explicit tapes are the standard source input.  Any conversion from a
compact request to these tapes must be a separately executed loader. -/
def initialConfiguration
    {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount)
    (inputTapes : Fin tapeCount → List Bool) :
    Configuration tapeCount stateCount where
  control := machine.start
  heads := fun _tape => 0
  tapes := inputTapes

structure ExecutionReceipt (tapeCount stateCount : ℕ) where
  final : Configuration tapeCount stateCount
  steps : ℕ
  peakTapeCells : ℕ

def runFrom
    {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount) :
    ℕ → Configuration tapeCount stateCount →
      Option (ExecutionReceipt tapeCount stateCount)
  | 0, configuration =>
      if machine.halted configuration.control then
        some
          { final := configuration
            steps := 0
            peakTapeCells := configuration.tapeCells }
      else none
  | fuel + 1, configuration =>
      if machine.halted configuration.control then
        some
          { final := configuration
            steps := 0
            peakTapeCells := configuration.tapeCells }
      else
        match step machine configuration with
        | none => none
        | some next =>
            match runFrom machine fuel next with
            | none => none
            | some suffix =>
                some
                  { final := suffix.final
                    steps := suffix.steps + 1
                    peakTapeCells := max configuration.tapeCells
                      suffix.peakTapeCells }

def run
    {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount)
    (fuel : ℕ) (inputTapes : Fin tapeCount → List Bool) :
    Option (ExecutionReceipt tapeCount stateCount) :=
  runFrom machine fuel (initialConfiguration machine inputTapes)

end NearCubicWires.LocalBitMultitape
end

/-! ## 5. Framing, programs, word functions and verifiers -/

section

namespace NearCubicWires.RepairOrdinary

open LocalBitMultitape

set_option autoImplicit false

def frame : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: frame bs

structure Program where
  tapeCount : ℕ
  stateCount : ℕ
  twoTapes : 2 ≤ tapeCount
  machine : Machine tapeCount stateCount
  outputTape : Fin tapeCount
  outputFresh : outputTape.val ≠ 0

def Program.inputTapes (p : Program) (word : List Bool) :
    Fin p.tapeCount → List Bool :=
  fun i => if i.val = 0 then frame word else []

structure WordFunction (Request : Type)
    (input output : Request → List Bool) (budget : Request → ℕ) where
  program : Program
  realizes : ∀ r, ∃ receipt,
    run program.machine (budget r) (program.inputTapes (input r)) = some receipt ∧
      receipt.final.tapes program.outputTape = output r

structure Verifier where
  tapeCount : ℕ
  stateCount : ℕ
  twoTapes : 2 ≤ tapeCount
  machine : Machine tapeCount stateCount
  accepting : Fin stateCount → Bool

def Verifier.inputTapes (v : Verifier)
    (input witness : List Bool) : Fin v.tapeCount → List Bool :=
  fun i => if i.val = 0 then frame input
    else if i.val = 1 then frame witness else []

def Verifier.acceptsAt (v : Verifier) (fuel : ℕ)
    (input witness : List Bool) : Prop :=
  ∃ receipt, run v.machine fuel (v.inputTapes input witness) = some receipt ∧
    v.accepting receipt.final.control = true

end NearCubicWires.RepairOrdinary
end

/-! ## 6. Ordinary programs, word functions, verifiers, hierarchies and weak machines; projection and literal codes -/

section

namespace NearCubicWires.RepairSource

open LocalBitMultitape CanonicalBinary

set_option autoImplicit false

abbrev frame := RepairOrdinary.frame

abbrev OrdinaryProgram := RepairOrdinary.Program

abbrev OrdinaryVerifier := RepairOrdinary.Verifier

end NearCubicWires.RepairSource
end

/-! ## 7. Oracle programs, NP verifiers and E^NP certificates -/

section

namespace NearCubicWires.RepairSource

open LocalBitMultitape

set_option autoImplicit false

structure OracleReturn (stateCount : ℕ) where
  onFalse : Fin stateCount
  onTrue : Fin stateCount

structure OrdinaryOracleProgram where
  base : OrdinaryProgram
  queryTape : Fin base.tapeCount
  queryFresh : queryTape.val ≠ 0
  query : Fin base.stateCount → Option (OracleReturn base.stateCount)

abbrev OrdinaryOracleProgram.Config (program : OrdinaryOracleProgram) :=
  Configuration program.base.tapeCount program.base.stateCount

/-- One step of an oracle program, with its cost: an ordinary machine step or an oracle query (see the
constructors). -/
inductive OrdinaryOracleStep (oracle : ℕ → Bool) (program : OrdinaryOracleProgram) :
    ℕ → program.Config → program.Config → Prop where
  | local (before after : program.Config)
      (notHalted : program.base.machine.halted before.control = false)
      (notQuery : program.query before.control = none)
      (transition : step program.base.machine before = some after) :
      OrdinaryOracleStep oracle program 1 before after
  | ask (before : program.Config) (bits padding : List Bool)
      (rule : OracleReturn program.base.stateCount)
      (notHalted : program.base.machine.halted before.control = false)
      (atQuery : program.query before.control = some rule)
      (rewound : before.heads program.queryTape = 0)
      (writtenQuery : before.tapes program.queryTape = frame bits ++ padding) :
      OrdinaryOracleStep oracle program ((frame bits).length + 1) before
        { before with control := if oracle (CanonicalBinary.bitsValue bits)
            then rule.onTrue else rule.onFalse }

inductive OrdinaryOracleTrace (oracle : ℕ → Bool) (program : OrdinaryOracleProgram) :
    ℕ → program.Config → program.Config → Prop where
  | refl (configuration : program.Config) :
      OrdinaryOracleTrace oracle program 0 configuration configuration
  | cons {cost rest : ℕ} {before middle after : program.Config}
      (step : OrdinaryOracleStep oracle program cost before middle)
      (tail : OrdinaryOracleTrace oracle program rest middle after) :
      OrdinaryOracleTrace oracle program (cost + rest) before after

/-- Inputs and outputs are framed, with a distinct initially blank output tape.
All data preparation, querying and final head movements inside the program
must be present in the counted trace. -/
def OrdinaryOracleRuns (oracle : ℕ → Bool) (program : OrdinaryOracleProgram)
    (input output : List Bool) (budget : ℕ) : Prop :=
  ∃ cost final, cost ≤ budget ∧
    OrdinaryOracleTrace oracle program cost
      (initialConfiguration program.base.machine (program.base.inputTapes input)) final ∧
    program.base.machine.halted final.control = true ∧
    final.tapes program.base.outputTape = frame output

/-- An NP verifier for the query predicate: an ordinary verifier whose time and witness length are
polynomial in the length of the binary query word `code.bits`, not in its numeric value. -/
structure EncodedNPVerifier (oracle : ℕ → Bool) where
  verifier : OrdinaryVerifier
  coefficient : ℕ
  coefficientPositive : 1 ≤ coefficient
  degree : ℕ
  correct : ∀ code : ℕ, oracle code = true ↔
    ∃ witness : List Bool,
      witness.length ≤ coefficient * (natBitLength code + 1) ^ degree ∧
      verifier.acceptsAt (coefficient * (natBitLength code + 1) ^ degree)
        code.bits witness

structure OrdinaryENPCertificate (oracle : ℕ → Bool) (language : Language) where
  program : OrdinaryOracleProgram
  exponent : ℕ
  exponentPositive : 1 ≤ exponent
  computes : ∀ n (input : BitInput n),
    OrdinaryOracleRuns oracle program (List.ofFn input) (language n input).toNat.bits
      (2 ^ (exponent * max 1 n))

end NearCubicWires.RepairSource
end

/-! ## 8. The main theorem's statement (`thm:main`): `MainStatement` -/

section

set_option autoImplicit false
namespace NearCubicGates.Target
open scoped BigOperators
open NearCubicWires

/-- A representation in the paper's class `𝒲` (`def:class`). Bottom weights are arbitrary
real numbers; signed integral top weights are charged by absolute value. -/
structure WeightedSymmetricCircuit (n : ℕ) where
  bottomCount : ℕ
  bottom : Fin bottomCount → RealThresholdGate n
  coefficient : Fin bottomCount → ℤ
  coefficient_ne_zero : ∀ i, coefficient i ≠ 0
  lookup : ℤ → Bool

def WeightedSymmetricCircuit.topWeight {n : ℕ}
    (C : WeightedSymmetricCircuit n) : ℕ :=
  ∑ i, (C.coefficient i).natAbs

noncomputable def WeightedSymmetricCircuit.score {n : ℕ}
    (C : WeightedSymmetricCircuit n) (x : BitInput n) : ℤ :=
  ∑ i, C.coefficient i * (if (C.bottom i).eval x then 1 else 0)

noncomputable def WeightedSymmetricCircuit.eval {n : ℕ}
    (C : WeightedSymmetricCircuit n) (x : BitInput n) : Bool :=
  C.lookup (C.score x)

noncomputable def agreement {n : ℕ} (C : WeightedSymmetricCircuit n)
    (F : Language) : ℝ :=
  ((Finset.univ.filter fun x : BitInput n => C.eval x = F n x).card : ℝ) /
    (Fintype.card (BitInput n) : ℝ)

/-- Ordinary deterministic exponential time with an NP oracle. This is an
actual finite-control execution certificate, not an uninterpreted predicate. -/
def InENP (F : Language) : Prop :=
  ∃ oracle : ℕ → Bool,
    Nonempty (RepairSource.EncodedNPVerifier oracle) ∧
    Nonempty (RepairSource.OrdinaryENPCertificate oracle F)

def lambda (n : ℕ) : ℕ := Nat.clog 2 n

def mu (n : ℕ) : ℕ := Nat.clog 2 (lambda n)

/-- The budget in integers, `(K·w·μ^7)^4·λ^21 ≤ n^12`. For `n ≥ 4` and `K > 0` it is equivalent to the paper's
`w ≤ ⌊n^3 / (K λ^(21/4) μ^7)⌋` (`thm:main`; SourceMapping/main-theorem.md). -/
def MainBudget (K n w : ℕ) : Prop :=
  (K * w * mu n ^ 7) ^ 4 * lambda n ^ 21 ≤ n ^ 12

/-- The conclusion of `thm:main`, for its fixed rational soundness gap. -/
def MainAt (gamma : ℚ) : Prop :=
  ∀ d : ℝ, 0 < d → d < (gamma : ℝ) / 5 →
    ∃ K : ℕ, 0 < K ∧ ∃ F : Language, InENP F ∧
      ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
        ∀ C : WeightedSymmetricCircuit n,
          MainBudget K n C.topWeight → agreement C F < 1 - d

/-- The paper's main theorem (`thm:main`, also labelled `thm:gadget-fixed-error`). -/
def MainStatement : Prop :=
  ∃ gamma : ℚ, 0 < gamma ∧ gamma < 1 ∧ MainAt gamma

end NearCubicGates.Target

end

/-! ## 9. Relative Hamming distance -/

section

set_option autoImplicit false
namespace NearCubicGates.PublishedSources.PCPP
open NearCubicWires
open NearCubicWires.RepairSource

noncomputable def relativeHamming {n : ℕ} (x y : BitInput n) : ℝ :=
  ((Finset.univ.filter fun i => x i ≠ y i).card : ℝ) / n

end NearCubicGates.PublishedSources.PCPP

end

/-! ## 10. Published statement: the prime number theorem as stated in Apostol, p. 74

Record of the transcription:

1. **Source.** T. M. Apostol, *Introduction to Analytic Number Theory*, Undergraduate Texts in Mathematics,
   Springer (1976), Chapter 4, §4.1 "Introduction", printed p. 74 (statement and the definition of `π(x)`);
   the analytic proof is Chapter 13 (the paper cites "Chapters 4 and 13" in `lem:primes` and in its source
   mapping, `app:sources`). Source PDF: the publisher's preview of Chapter 4 (Springer, doi
   10.1007/978-1-4757-5579-4_5), sha256 `812bf5275a7717f606be81ac5837f36382015be99ee7719e199c7b2ed9ac9c32`.
   The PDF's text layer garbles `π` as `n:` and drops the fraction bar; the quotations below are read from the
   printed page and agree with the text layer up to those extraction artefacts.
2. **Proposition.** `NearCubicGates.Published.Apostol.primeNumberTheorem`, with the model
   `NearCubicGates.Published.Apostol.primeCountingReal` (the real-argument prime count). Mathlib's
   `Nat.primeCounting` is not used in the statement (its argument is natural).
3. **Quantifier ledger.** One limit as the real variable `x → +∞`. No rate, no effective onset, no uniformity:
   for each neighbourhood of `1` the threshold beyond which the quotient stays in it is merely asserted to exist.
4. **Source hypotheses.** None besides `x > 0` in the definition of `π(x)` (see 5).
5. **Conventions.** `π(x)` counts primes `p` with `p ≤ x` ("not exceeding", endpoint included). `log` is the
   natural logarithm (Apostol's `log`; `Real.log`). The quotient is `(π(x) · log x) / x`. Apostol defines
   `π(x)` for `x > 0`; `primeCountingReal` is total (it is `0` for `x < 2`), which does not affect a limit at
   `+∞` (`Filter.atTop` on `ℝ`).
6. **Consumer.** `NearCubicGates.Adapters.Base.primes_of_primeNumberTheorem`
   (`SourceAdapters/Base/Primes.lean`), which proves `NineInputs.primes`
   (`NearCubicGates.PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem`: natural arguments, an onset
   `≥ 2` for each `ε > 0`, strict absolute error).

**What is NOT claimed.** No error term or rate, no statement about primes in short intervals, nothing about the
Chebyshev functions of §4.2, and no statement at natural arguments (that specialization is a proof in the
adapter). Vacuity: the statement has no hypotheses; `SourceAdapters/Vacuity/Apostol.lean` checks the endpoint
convention.
-/

section

set_option autoImplicit false

namespace NearCubicGates.Published.Apostol

/-- Apostol p. 74, §4.1: "If x > 0 let π(x) denote the number of primes not exceeding x."

The number of primes `p` with `p ≤ x`, for a real `x`. -/
noncomputable def primeCountingReal (x : ℝ) : ℕ :=
  Set.ncard {p : ℕ | p.Prime ∧ (p : ℝ) ≤ x}

/-- **The prime number theorem**, Apostol p. 74, §4.1: "… to conjecture that π(x) is asymptotic
to x/log x, that is,
  lim_{x→∞} π(x)log x / x = 1.
This conjecture was first proved in 1896 by Hadamard [28] and de la Vallée Poussin [71] and is known now as the
prime number theorem." (Proof: Chapter 13.)

As `x → +∞` through the reals, `π(x) · log x / x` tends to `1`. -/
def primeNumberTheorem : Prop :=
  Filter.Tendsto (fun x : ℝ => (primeCountingReal x : ℝ) * Real.log x / x) Filter.atTop (nhds 1)

end NearCubicGates.Published.Apostol

end

/-! ## 11. BCGT13: the strong PCPP verifiers `V_RS`, `V_VRS` and their soundness (published statements)

Record of the transcription.

1. **Source.** E. Ben-Sasson, A. Chiesa, D. Genkin, E. Tromer, "On the concrete efficiency of
   probabilistically-checkable proofs", ECCC TR12-045, revision 3 (December 28, 2012; full version). Source PDF
   (ECCC download of revision 3): sha256
   `9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0`.
   Locators (page of that PDF, which is also the printed page number): Def 4.1–4.4 p.18; Def 4.7 p.18; Def 4.15
   p.20; Theorem 11.1 p.51; Eq. (6) of Theorem 11.3 p.53; Def 12.14, Remark 12.15 p.75; Lemmas 12.16–12.20 (the
   non-adaptive `Q`/`D` listings) p.75–84; Algorithms 12–16 p.118–122; Algorithms 19–21, 23 p.124–128;
   Lemma C.1 p.131; Lemma C.9 (recursion (27)) p.134; Lemma C.10 (recursion (28)) pp.136–137.
   **Read from the printed page, not the PDF's text layer:** Theorem 11.1 (p.51: both soundness bounds, all seven
   conditions, the constant `c`; floor vs ceiling in conditions 4–5 checked at 400 dpi); Lemma C.3 (p.132).
2. **Statements.** `BCGT13_Theorem11_1` (with Def 4.15), about the verifiers transcribed in this file (Mathlib
   otherwise).
3. **Quantifier ledger.** For every tuple `(η, κ0, γ, μ)` satisfying Eq. (6) (here: natural numbers, a weakening
   of "any integers"), every field `F_{2^ℓ}`, every affine subspace `S` given by a basis `B_S` and offset `O_S`,
   every degree `d < |S|`, and (for VRS) every affine `H ⊆ S` with `|H| ≤ d`: completeness and soundness of the
   verifiers defined below for that tuple.
   The printed constant is undefined when `e2 = 0`, which Eq. (6) permits (e.g. `(3,5,2,2)`), so the statement
   below is restricted to `e1 > 0 ∧ e2 > 0`, where that formula is defined.
4. **Source hypotheses kept.** Eq. (6); `d < |S|` (Def 4.4's "the polynomial corresponding to p" is unique only
   then); `|H| ≤ d` (Algorithm 12 note: "it must be that d ≥ |H|").
5. **Conventions and transcription decisions** (each is a reading to check against the source):
   - `F_{2^ℓ}` is any finite field of characteristic two with `2^ℓ` elements (the source's `F_2(x)`; every such
     field is isomorphic to it, and no algorithm here reads the representation).
   - Bases are lists `B = (a_1, …, a_κ)`. GetRandElt (Alg. 19): `Σ_j r_j a_j + O`. GetEltWithIndex (Alg. 20):
     "i_1 ⋯ i_κ is (i − 1) in binary" is read **least significant bit first** (`i_j` is bit `j−1`), as in
     SubspaceEval / SubspaceInterp (Alg. 22–23: `α_{Σ b_i 2^{i−1}}`). This is the only order under which the row and
     column branches of `Translate` (§12.3.1) address the same cell of `f`. GetIndexOfElt (used in §12.3, not
     listed): the least index `i ∈ {1, …, 2^κ}` with GetEltWithIndex `= α` (0 if none).
   - FindSubspPoly (Alg. 21) outputs a circuit for "the vanishing polynomial for the affine subspace S"; we use
     its value `Z_S(x) = ∏_{s ∈ S} (x − s)`.
   - SubspaceInterp (Alg. 23) is used only through its output specification ("P … with d < 2^κ, such that P takes
     the given values on S"): the base cases of `D_{RS,=}` and of `D_RS` (`κ ≤ η`) accept iff the answers are the
     values on `S`, in GetEltWithIndex order, of a polynomial of degree at most the bound ("directly verifies
     whether α_1 ⋯ α_{2^κ} is in RS(F_{2^ℓ}, L, |L|/2^η − 1)", p.76). (The printed Alg. 23 base case
     `(x − α_{j2^κ})·(x − α_{j2^κ+1})` is not an interpolation.)
   - Indices are 1-based into the concatenation (implicit input in GetEltWithIndex order, then the proof). A
     query `⊥` (§12.3.3) and an index outside `{1, …, |S| + length}` are answered by `0`.
   - Recursions use fuel `κ` (the dimension); under Eq. (6) the dimensions `⌊κ/2⌋ − γ + μ + 1` and `⌈κ/2⌉ + γ`
     are below `κ` whenever `κ > κ0`, so the fuel is never exhausted.
   - Coins: the verifier's random string is a list `r_1 r_2 ⋯`; sub-calls read the prefixes or suffixes the listings
     name (`r^{(z)} := r_1 ⋯`, `r_{m+1} ⋯`).
   - **§12.3.5 vs Algorithm 12 (decision rule taken from Algorithm 12).** `Q_VRS` sends query `q_RS + 1` to `p(α)`
     and `q_RS + 2` to `p̃(α)`; `D_VRS` parses them as `ω̃ ω` and tests `ω = τ·ω̃`, i.e. `p̃(α) = Z_H(α)·p(α)`.
     Algorithm 12 step 2(g) tests `p(α) = ω·p̃(α)` with `ω = Z_H(α)`. Under the §12.3.5 reading the honest proof
     is rejected, so we follow Algorithm 12, which Theorem 11.1 names.
   - **§12.3.3 (V_RS,>).** `Q_{RS,>}` reserves `1 + 2^η` consistency slots, the unused ones `⊥`; `D_{RS,>}` sums
     `γ^{i(d_{κ,η}+1)} v_i` over all `i < 2^η`. With `⊥ ↦ 0` this is Algorithm 14's sum over `i < m` (resp.
     `i ≤ m`). Step (g)vi's "if i = m + 2" is read `i0 = m + 2`. The query count is the listing's
     `m·q_{RS,=} + 𝟏·q_{RS,<} + 1 + 2^η` (Lemma C.3 prints `… + m + 𝟏 + 1`, and its `m := ⌈(d+1)/(d_{κ,η}+1)⌉`
     contradicts Algorithm 14's floor; C.3 is not used).
   - **§12.3.1 typos.** Translate xi.D outputs `(text, α, i)` (read: `elt`); viii.B omits `O_L` from
     GetIndexOfElt; `query_{RS,=}(ℓ, κ)` is defined as the largest number of base-case queries over the coin
     paths (the C.1 proof's "0 if κ > κ0" is a typo).
   - `D_{RS,<}` "is independent of d" (p.80) is false (step 6(b)ii uses `d`); we transcribe the steps.
6. **What is NOT claimed.** No running time (the source states none for these verifiers: footnote 18,
   p.31; footnote 34, p.131; §12.3, p.75). No prover efficiency. No statement for `d ≥ |S|`.
   Nothing about the amplified verifiers `V_aRS`, `V_aVRS` or about `V_sACSP`. Lemmas C.1–C.5 are not stated here: for
   the transcribed recursions and verifiers they are computations (proved in `SourceAdapters`; Lemma C.1 for the one
   tuple used, since its printed length bound does not hold for every tuple satisfying Eq. (6)).
7. **Consumer.** `NearCubicGates.Adapters.ShortPCP` (the single-run verifier `V0` of Step 2 of the paper's
   `thm:short-pcp-ours`), towards `MW20_OracleCircuitPCP_TM2`. Completeness of single runs is taken from
   Def 4.15(1) via Theorem 11.1's "(strong) PCPP verifiers"; the paper's proof of that step derives it instead from
   Theorem 8.1 and Lemmas C.6–C.7.
-/

section

set_option autoImplicit false

namespace NearCubicGates.Published.BCGT13

open Finset Polynomial

/-! ## Theorem 11.1: the parameter conditions (Eq. (6)) and the constant `c` -/

/-- `⌊z/2⌋`. -/
def floorHalf (z : ℤ) : ℤ := Int.fdiv z 2
/-- `⌈z/2⌉`. -/
def ceilHalf (z : ℤ) : ℤ := -Int.fdiv (-z) 2

/-- `(3 + (−1)^{κ0 mod 2})/2`. -/
def sThree (κ0 : ℤ) : ℤ := Int.fdiv (3 + (-1) ^ (κ0 % 2).toNat) 2
/-- `(1 + (−1)^{κ0 mod 2})/2`. -/
def sOne (κ0 : ℤ) : ℤ := Int.fdiv (1 + (-1) ^ (κ0 % 2).toNat) 2

/-- Theorem 11.1 (= Eq. (6) of Theorem 11.3), p.51: "(η, κ0, γ, μ) are any integers satisfying
min{⌊(κ0+1)/2⌋ − γ, ⌈(κ0+1)/2⌉ + γ} ≥ 1,
max{⌊(κ0+1)/2⌋ − γ + μ + 1, ⌈(κ0+1)/2⌉ + γ} ≤ κ0,
min{⌊(κ0+1)/2⌋ − γ + μ + 1, ⌈(κ0+1)/2⌉ + γ} ≥ η + 1,
κ0 + (3+(−1)^{κ0 mod 2})/2 > ⌊(κ0 + (3+(−1)^{κ0 mod 2})/2)/2⌋ − γ + μ + 1,
κ0 + (1+(−1)^{κ0 mod 2})/2 > ⌊(κ0 + (1+(−1)^{κ0 mod 2})/2)/2⌋ + γ,
μ + 1 ≥ η ≥ max{2, μ + 1}, μ ≥ γ". -/
def Equation6 (η κ0 γ μ : ℤ) : Prop :=
  min (floorHalf (κ0 + 1) - γ) (ceilHalf (κ0 + 1) + γ) ≥ 1 ∧
  max (floorHalf (κ0 + 1) - γ + μ + 1) (ceilHalf (κ0 + 1) + γ) ≤ κ0 ∧
  min (floorHalf (κ0 + 1) - γ + μ + 1) (ceilHalf (κ0 + 1) + γ) ≥ η + 1 ∧
  κ0 + sThree κ0 > floorHalf (κ0 + sThree κ0) - γ + μ + 1 ∧
  κ0 + sOne κ0 > floorHalf (κ0 + sOne κ0) + γ ∧
  μ + 1 ≥ η ∧ η ≥ max 2 (μ + 1) ∧
  μ ≥ γ

instance (η κ0 γ μ : ℤ) : Decidable (Equation6 η κ0 γ μ) := by
  unfold Equation6; infer_instance

/-- Theorem 11.1, p.51: "c := (a + b/2 + √(b(b+4a))/2)^{1/min{e1,e2}}, where c0 := 4/(1 − 1/2^{η−1} −
1/2^η)², a := 2^{η+1}(1+c0)/(2^{η−1} − 1), b := 2^{μ+2}, e1 := log((κ0 + (3+(−1)^{κ0 mod 2})/2) /
(⌊(κ0 + (3+(−1)^{κ0 mod 2})/2)/2⌋ − γ + μ + 1)), e2 := log((κ0 + (1+(−1)^{κ0 mod 2})/2) /
(⌈(κ0 + (1+(−1)^{κ0 mod 2})/2)/2⌉ + γ))". -/
noncomputable def constC (η κ0 γ μ : ℤ) : ℝ :=
  let c0 : ℝ := 4 / (1 - 1 / (2 : ℝ) ^ (η - 1) - 1 / (2 : ℝ) ^ η) ^ 2
  let a : ℝ := (2 : ℝ) ^ (η + 1) * (1 + c0) / ((2 : ℝ) ^ (η - 1) - 1)
  let b : ℝ := (2 : ℝ) ^ (μ + 2)
  let e1 : ℝ := Real.logb 2 (((κ0 + sThree κ0 : ℤ) : ℝ) / ((floorHalf (κ0 + sThree κ0) - γ + μ + 1 : ℤ) : ℝ))
  let e2 : ℝ := Real.logb 2 (((κ0 + sOne κ0 : ℤ) : ℝ) / ((ceilHalf (κ0 + sOne κ0) + γ : ℤ) : ℝ))
  (a + b / 2 + Real.sqrt (b * (b + 4 * a)) / 2) ^ (1 / min e1 e2)

/-- `(2^{η+1} + κ^{log c}) / (1 − 2^{−η})`, the common term of both soundness functions of Theorem 11.1. -/
noncomputable def soundTerm (η κ0 γ μ : ℤ) (κ : ℕ) : ℝ :=
  ((2 : ℝ) ^ (η + 1) + (κ : ℝ) ^ Real.logb 2 (constC η κ0 γ μ)) / (1 - (2 : ℝ) ^ (-η))

/-- A parameter tuple `(η, κ0, γ, μ)` (natural numbers). -/
structure Tuple where
  η : ℕ
  κ0 : ℕ
  γ : ℕ
  μ : ℕ

/-- Eq. (6) for a natural tuple. -/
def Tuple.Valid (T : Tuple) : Prop := Equation6 T.η T.κ0 T.γ T.μ

/-- The positive-exponent domain of `1/min{e1,e2}` in Theorem 11.1, p.51. -/
def Tuple.PositiveExponents (T : Tuple) : Prop :=
  0 < Real.logb 2 (((T.κ0 + sThree T.κ0 : ℤ) : ℝ) /
    ((floorHalf (T.κ0 + sThree T.κ0) - T.γ + T.μ + 1 : ℤ) : ℝ)) ∧
  0 < Real.logb 2 (((T.κ0 + sOne T.κ0 : ℤ) : ℝ) /
    ((ceilHalf (T.κ0 + sOne T.κ0) + T.γ : ℤ) : ℝ))

/-! ## Codes, distance, affine subspaces (Defs 4.3, 4.4, 4.7; Algorithms 19–21) -/

section Model

variable {F : Type} [Field F] [DecidableEq F]

/-- Algorithm 19 (GetRandElt): "α := Σ_{j=1}^κ r_j a_j + O_S" (missing bits read as 0, extra bits ignored). -/
def getRandElt (B : List F) (O : F) (r : List Bool) : F :=
  (List.zipWith (fun a b => if b then a else 0) B r).sum + O

/-- Algorithm 20 (GetEltWithIndex): "α := (Σ_{j=1}^κ i_j a_j) + O_S, … i_1 ⋯ i_κ is (i − 1) in binary"
(least significant bit first, see the header). -/
def eltWithIndex (B : List F) (O : F) (i : ℕ) : F :=
  getRandElt B O ((List.range B.length).map fun j => (i - 1).testBit j)

/-- GetIndexOfElt: the least `i ∈ {1, …, 2^κ}` with `GetEltWithIndex(B, O, i) = α`, and `0` if there is none. -/
def indexOfElt (B : List F) (O : F) (α : F) : ℕ :=
  (((List.range (2 ^ B.length)).find? fun i => eltWithIndex B O (i + 1) = α).map (· + 1)).getD 0

/-- The affine subspace with basis `B` and offset `O`: its `2^κ` points in GetEltWithIndex order. -/
def span (B : List F) (O : F) : Finset F :=
  ((List.range (2 ^ B.length)).map fun i => eltWithIndex B O (i + 1)).toFinset

/-- "`B_S` and `O_S`, basis and offset for the `κ`-dimensional affine subspace `S`": the points are distinct. -/
def IsBasis (B : List F) (O : F) : Prop := (span B O).card = 2 ^ B.length

/-- Algorithm 21 (FindSubspPoly): the value of "the vanishing polynomial for the affine subspace S". -/
def zEval (B : List F) (O : F) (x : F) : F := ∏ s ∈ span B O, (x - s)

/-- Def 4.7, fractional Hamming distance of functions on the evaluation set `S`. -/
noncomputable def fracDist (S : Finset F) (p q : F → F) : ℝ :=
  ((S.filter fun s => p s ≠ q s).card : ℝ) / (S.card : ℝ)

/-- Def 4.3, "RS(F, S, d) := {p : S → F s.t. p is an evaluation of a polynomial of degree at most d over S}". -/
def RS (S : Finset F) (d : ℕ) : Set (F → F) :=
  {p | ∃ P : F[X], P.natDegree ≤ d ∧ ∀ s ∈ S, p s = P.eval s}

/-- Def 4.4, "VRS(F, S, H, d) := {p ∈ RS(F, S, d) s.t. the polynomial corresponding to p vanishes on H}". -/
def VRS (S H : Finset F) (d : ℕ) : Set (F → F) :=
  {p | ∃ P : F[X], P.natDegree ≤ d ∧ (∀ s ∈ S, p s = P.eval s) ∧ ∀ h ∈ H, P.eval h = 0}

/-- The base-case test: the answers `α_1, …, α_{2^κ}` are, in GetEltWithIndex order, the values on the subspace
of a polynomial of degree at most `deg` (SubspaceInterp, then "if d̃ ≤ d, output 1, else output 0"). -/
noncomputable def degreeTest (B : List F) (O : F) (deg : ℕ) (ans : ℕ → F) : Bool :=
  @decide (∃ P : F[X], P.natDegree ≤ deg ∧ ∀ i < 2 ^ B.length, P.eval (eltWithIndex B O (i + 1)) = ans (i + 1))
    (Classical.propDecidable _)

end Model

/-! ## Lemma C.9, C.10 and the query count of `V_RS,=` -/

/-- `d_{κ,η} := |S|/2^η − 1 = 2^κ/2^η − 1`. -/
def dKE (κ η : ℕ) : ℕ := 2 ^ κ / 2 ^ η - 1

/-- `m_{κ,η,d} := ⌊(d+1)/(d_{κ,η}+1)⌋` (Algorithm 14 step 2(b); §12.3.3). -/
def mKED (κ η d : ℕ) : ℕ := (d + 1) / (dKE κ η + 1)

/-- `rand_{RS,=}(ℓ, κ)`: recursion (27) of Lemma C.9, "r(κ) = 0 if κ ≤ κ0, 1 + max{⌈κ/2⌉ + γ +
r(⌊κ/2⌋ − γ + μ + 1), ⌊κ/2⌋ − γ + μ + r(⌈κ/2⌉ + γ)} if κ > κ0" (fuel `n`). -/
def randEqF (T : Tuple) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, κ =>
    if κ ≤ T.κ0 then 0 else
      1 + max ((κ + 1) / 2 + T.γ + randEqF T n (κ / 2 - T.γ + T.μ + 1))
        (κ / 2 - T.γ + T.μ + randEqF T n ((κ + 1) / 2 + T.γ))

/-- `length_{RS,=}(ℓ, κ)`: recursion (28) of Lemma C.10, "r(κ) = 0 if κ ≤ κ0, 2^{⌈κ/2⌉+γ}·2^{⌊κ/2⌋−γ+μ+1} +
2^{⌈κ/2⌉+γ}·r(⌊κ/2⌋ − γ + μ + 1) + 2^{⌊κ/2⌋−γ+μ}·r(⌈κ/2⌉ + γ) if κ > κ0" (fuel `n`). -/
def lengthEqF (T : Tuple) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, κ =>
    if κ ≤ T.κ0 then 0 else
      2 ^ ((κ + 1) / 2 + T.γ) * 2 ^ (κ / 2 - T.γ + T.μ + 1) +
        2 ^ ((κ + 1) / 2 + T.γ) * lengthEqF T n (κ / 2 - T.γ + T.μ + 1) +
        2 ^ (κ / 2 - T.γ + T.μ) * lengthEqF T n ((κ + 1) / 2 + T.γ)

/-- `query_{RS,=}(ℓ, κ)`: `2^κ` base-case queries if `κ ≤ κ0`, else the larger of the two recursive calls. -/
def queryEqF (T : Tuple) : ℕ → ℕ → ℕ
  | 0, κ => 2 ^ κ
  | n + 1, κ =>
    if κ ≤ T.κ0 then 2 ^ κ else max (queryEqF T n (κ / 2 - T.γ + T.μ + 1)) (queryEqF T n ((κ + 1) / 2 + T.γ))

/-- `rand_{RS,=}(ℓ, κ)`. -/
def randEq (T : Tuple) (κ : ℕ) : ℕ := randEqF T κ κ
/-- `length_{RS,=}(ℓ, κ)`. -/
def lengthEq (T : Tuple) (κ : ℕ) : ℕ := lengthEqF T κ κ
/-- `query_{RS,=}(ℓ, κ)`. -/
def queryEq (T : Tuple) (κ : ℕ) : ℕ := queryEqF T κ κ

/-! ## `V_RS,=` (Lemma 12.16: `Translate`, `Q_{RS,=}`, `D_{RS,=}`; Algorithm 16) -/

section Verifiers

variable {F : Type} [Field F] [DecidableEq F]

/-- The output of `Translate`: a query to the implicit input at a point (with its index), or to the proof. -/
inductive TrOut (F : Type) where
  | inp (α : F) (j : ℕ)
  | prf (j : ℕ)

/-- `Translate(I_ℓ, B_L, O_L, r, i)` of §12.3.1 (fuel `n`). -/
def translate (T : Tuple) : ℕ → List F → F → List Bool → ℕ → TrOut F
  | 0, B, O, _, i => .inp (eltWithIndex B O i) i
  | n + 1, B, O, r, i =>
    if B.length ≤ T.κ0 then
      -- 1. "αi := GetEltWithIndex(I_ℓ, B_L, O_L, i); text := implicit-input; elt := αi; output (text, elt, i)"
      .inp (eltWithIndex B O i) i
    else
      let κ := B.length
      let k := κ / 2 - T.γ                        -- dim L0
      let BL0 := B.take k                           -- (a) B_{L0} := (a_1, …, a_{⌊κ/2⌋−γ}), O_{L0} := O_L
      let BL00 := B.take (k + T.μ)                  -- (b) B_{L00} := (a_1, …, a_{⌊κ/2⌋−γ+μ}), O_{L00} := O_L
      let z : F → F := zEval BL0 O                  -- (c) [Z_{L0}]_A
      let BL1 := B.drop k                           -- B_{L1} := (a_{⌊κ/2⌋−γ+1}, …, a_κ), O_{L1} := O_L
      let nL := 2 ^ κ                               -- |L|
      let nLb := 2 ^ (k + T.μ + 1)                  -- |L_β|
      let nL1 := 2 ^ BL1.length                     -- |L1|
      if r.head? = some false then
        -- (d) row test translation
        let m := 1 + BL1.length                     -- i. m := 1 + ⌈κ/2⌉ + γ
        let β := getRandElt BL1 O ((r.drop 1).take BL1.length)   -- iii.
        let β' := z β                               -- iv.
        let ιβ := indexOfElt BL1 O β                -- v.
        let BLb := if β ∈ span BL00 O then BL00 ++ [B.getD (k + T.μ) 0] else BL00 ++ [β + O]  -- vi.–viii.
        match translate T n BLb O (r.drop m) i with  -- ix.
        | .inp α ι =>                              -- x.
          if z α = β' then .inp α (indexOfElt B O α)                       -- C.
          else .prf (nL + nLb * (ιβ - 1) + ι)                               -- D.
        | .prf ι =>                                 -- xi. C.
          .prf ((ι - nLb + nL) + nLb * nL1 + (ιβ - 1) * lengthEq T (k + T.μ + 1))
      else
        -- (e) column test translation
        let m := 1 + (k + T.μ)                      -- i. m := 1 + ⌊κ/2⌋ − γ + μ
        let α := getRandElt BL00 O ((r.drop 1).take (k + T.μ))   -- ii.
        let α' := z α                               -- iii.
        let ια := indexOfElt BL00 O α               -- iv.
        let BZ := BL1.map fun a => z a + z 0        -- v. B_{Z_{L0}(L1)}
        let OZ := z O                               -- vi. O_{Z_{L0}(L1)} := [Z_{L0}]_A(O_{L1})
        match translate T n BZ OZ (r.drop m) i with  -- vii.
        | .inp β' ι =>                              -- viii.
          if α' = β' then .inp α (indexOfElt B O α)                         -- B.
          else .prf (nL + nLb * (ι - 1) + ια)                               -- C.
        | .prf ι =>                                 -- ix. C.
          .prf ((ι - 2 ^ BZ.length + nL) + nLb * nL1 + nL1 * lengthEq T (k + T.μ + 1) +
            (ια - 1) * lengthEq T BZ.length)

/-- `Q_{RS,=}((I_ℓ, B_L, O_L), r, i)`: "Compute (text, elt, j) := Translate(I_ℓ, B_L, O_L, r, i). Output j." -/
def qEq (T : Tuple) (B : List F) (O : F) (r : List Bool) (i : ℕ) : Option ℕ :=
  match translate T B.length B O r i with
  | .inp _ j => some j
  | .prf j => some j

/-- `D_{RS,=}((I_ℓ, B_L, O_L), r, α_1 ⋯)` of §12.3.1 (fuel `n`). -/
noncomputable def dEqF (T : Tuple) : ℕ → List F → F → List Bool → (ℕ → F) → Bool
  | 0, B, O, _, ans => degreeTest B O (dKE B.length T.η) ans
  | n + 1, B, O, r, ans =>
    if B.length ≤ T.κ0 then
      -- 1. "d_{κ,η} = 2^κ/2^η − 1; P := SubspaceInterp(…); d̃ := deg(P); if d̃ ≤ d_{κ,η}, output 1, else output 0"
      degreeTest B O (dKE B.length T.η) ans
    else
      let κ := B.length
      let k := κ / 2 - T.γ
      let BL0 := B.take k
      let BL00 := B.take (k + T.μ)
      let z : F → F := zEval BL0 O
      let BL1 := B.drop k
      if r.head? = some false then
        let m := 1 + BL1.length
        let β := getRandElt BL1 O ((r.drop 1).take BL1.length)
        let BLb := if β ∈ span BL00 O then BL00 ++ [B.getD (k + T.μ) 0] else BL00 ++ [β + O]
        dEqF T n BLb O (r.drop m) ans
      else
        let m := 1 + (k + T.μ)
        dEqF T n (BL1.map fun a => z a + z 0) (z O) (r.drop m) ans

/-- `D_{RS,=}`. -/
noncomputable def dEq (T : Tuple) (B : List F) (O : F) (r : List Bool) (ans : ℕ → F) : Bool :=
  dEqF T B.length B O r ans

/-! ## Flat verifiers: randomness, queries, length, `Q`, `D` -/

/-- A verifier as §12.3 decomposes it: `rand` coins, `query` queries, proof `length` (field elements); `Q r i`
is the 1-based index of the `i`-th query into the concatenation of the implicit input (`|S|` entries) and the
proof, or `none` (`⊥`); `D r ans` decides from the answers `ans 1, ans 2, …`. -/
structure FlatVerifier (F : Type) where
  rand : ℕ
  query : ℕ
  length : ℕ
  Q : List Bool → ℕ → Option ℕ
  D : List Bool → (ℕ → F) → Bool

/-- `V_{RS,=}` on `(I_ℓ, B_L, O_L)` (degree `|L|/2^η − 1`). -/
noncomputable def vEq (T : Tuple) (B : List F) (O : F) : FlatVerifier F where
  rand := randEq T B.length
  query := queryEq T B.length
  length := lengthEq T B.length
  Q := qEq T B O
  D := dEq T B O

/-- `V_{RS,<}` on `(I_ℓ, B_S, O_S, d)`, §12.3.2 (`Q_{RS,<}`, `D_{RS,<}`; Algorithm 15). -/
noncomputable def vLt (T : Tuple) (B : List F) (O : F) (d : ℕ) : FlatVerifier F where
  rand := randEq T B.length
  query := 2 * queryEq T B.length
  length := 2 * lengthEq T B.length
  Q := fun r i =>
    let qE := queryEq T B.length
    if 1 ≤ i ∧ i ≤ qE then qEq T B O r i
    else
      -- 2. ι := i − query_{RS,=}; j′ := Q_{RS,=}(…, ι); shift proof indices by length_{RS,=}
      match qEq T B O r (i - qE) with
      | some j' => if 0 < j' ∧ j' ≤ 2 ^ B.length then some j' else some (lengthEq T B.length + j')
      | none => none
  D := fun r ans =>
    let qE := queryEq T B.length
    -- 3. b1 := D_{RS,=}(…, α′)
    let b1 := dEq T B O r ans
    -- 6. reset α″_i to γ_{j′}^{d_{κ,η} − d} α″_i when the i-th query of the second call is to the implicit input
    let ans2 : ℕ → F := fun i =>
      match qEq T B O r i with
      | some j' =>
        if 0 < j' ∧ j' ≤ 2 ^ B.length then
          eltWithIndex B O j' ^ (dKE B.length T.η - d) * ans (qE + i)
        else ans (qE + i)
      | none => ans (qE + i)
    -- 7.–9. b := b1 ∧ b2
    b1 && dEq T B O r ans2

/-- `V_{RS,>}` on `(I_ℓ, B_S, O_S, d)`, §12.3.3 (`Q_{RS,>}`, `D_{RS,>}`; Algorithm 14), for `d < 2^κ`. -/
noncomputable def vGt (T : Tuple) (B : List F) (O : F) (d : ℕ) : FlatVerifier F :=
  let κ := B.length
  let nS := 2 ^ κ
  let D' := dKE κ T.η
  let m := mKED κ T.η d                              -- (b)
  let dd := d - m * (D' + 1)                         -- (c) d_{κ,η,d}
  let one : Bool := decide (m * (D' + 1) < d + 1)
  let qE := queryEq T κ
  let lE := lengthEq T κ
  let vL := vLt T B O dd
  let qL := if one then vL.query else 0
  { rand := max (max (randEq T κ) (if one then randEq T κ else 0)) κ
    query := m * qE + qL + 1 + 2 ^ T.η
    length := m * (nS + lE) + (if one then nS + vL.length else 0)
    Q := fun r i =>
      if d ≥ nS then none                            -- 1. output ⊥
      else if 1 ≤ i ∧ i ≤ m * qE then                -- (d)
        let zz := (i - 1) / qE
        (qEq T B O r (i - zz * qE)).map fun j' => nS + zz * (nS + lE) + j'
      else if one ∧ 1 ≤ i - m * qE ∧ i - m * qE ≤ qL then   -- (e)
        (vL.Q r (i - m * qE)).map fun j' => nS + m * (nS + lE) + j'
      else                                            -- (f), (g): the consistency queries
        let i0 := i - (m * qE + qL)
        let γ := getRandElt B O (r.take κ)
        let ιγ := indexOfElt B O γ
        if i0 = 1 then some ιγ
        else if 1 < i0 ∧ i0 ≤ m + 1 then some (nS + (i0 - 2) * (nS + lE) + ιγ)
        else if one ∧ i0 = m + 2 then some (nS + m * (nS + lE) + ιγ)
        else none
    D := fun r ans =>
      if d ≥ nS then true                            -- 1. output 1
      else
        let γ := getRandElt B O (r.take κ)           -- (a), (b)
        -- ii. b_i := D_{RS,=}(…, α^{(i)}) for i < m; iv. b_m := D_{RS,<}(…, α^{(m)}) when 𝟏 = 1
        let bs := (List.range m).all fun z => dEq T B O r fun i => ans (z * qE + i)
        let bm := if one then vL.D r (fun i => ans (m * qE + i)) else true
        -- v. b_consist := (v = Σ_{i=0}^{2^η−1} γ^{i(d_{κ,η}+1)} v_i), with ⊥-answers 0
        let base := m * qE + qL
        let v := ans (base + 1)
        let bc := decide (v = ∑ i ∈ Finset.range (2 ^ T.η), γ ^ (i * (D' + 1)) * ans (base + 2 + i))
        bc && bs && bm }

/-- `V_RS` on `(I_ℓ, B_S, O_S, d)`, §12.3.4 (`Q_RS`, `D_RS`; Algorithm 13): for `κ ≤ η` the direct degree test
(`Q`: "output j := i"; `D`: SubspaceInterp and "if d̃ ≤ d output 1"), otherwise `V_{RS,<}`, `V_{RS,=}`, `V_{RS,>}`
as `d <`, `=`, `> d_{κ,η}`. -/
noncomputable def vRS (T : Tuple) (B : List F) (O : F) (d : ℕ) : FlatVerifier F :=
  if B.length ≤ T.η then
    { rand := 0, query := 2 ^ B.length, length := 0, Q := fun _ i => some i, D := fun _ ans => degreeTest B O d ans }
  else if d < dKE B.length T.η then vLt T B O d
  else if d = dKE B.length T.η then vEq T B O
  else vGt T B O d

/-- `V_VRS` on `(I_ℓ, B_S, O_S, B_H, O_H, d)`, §12.3.5 (`Q_VRS`) with the decision of Algorithm 12 (see the
header): the proof is `(p̃, π̃)`; `V_RS` tests `p̃` against degree `d − |H|`; then `p(α) = Z_H(α)·p̃(α)`. -/
noncomputable def vVRS (T : Tuple) (B : List F) (O : F) (BH : List F) (OH : F) (d : ℕ) : FlatVerifier F :=
  let κ := B.length
  let nS := 2 ^ κ
  let V := vRS T B O (d - 2 ^ BH.length)
  { rand := max V.rand κ
    query := V.query + 2
    length := nS + V.length
    Q := fun r i =>
      if 1 ≤ i ∧ i ≤ V.query then (V.Q r i).map fun j => nS + j      -- 1. j := |S| + j_old
      else
        let α := getRandElt B O (r.take κ)
        if i = V.query + 1 then some (indexOfElt B O α)               -- 2. query α to p
        else if i = V.query + 2 then some (nS + indexOfElt B O α)      -- 3. query α to p̃
        else none
    D := fun r ans =>
      let bRS := V.D r ans                                            -- 3. b_RS
      let α := getRandElt B O (r.take κ)                              -- 4.–5.
      let τ := zEval BH OH α                                          -- 6.–7.
      -- Algorithm 12 step 2(g): "if p(α) = ω · p̃(α), then b_consist := 1"
      bRS && decide (ans (V.query + 1) = τ * ans (V.query + 2)) }

/-- The answers to the queries of `V` on coins `r`, implicit input `p` (on `S` with basis `B`, offset `O`) and proof
`π`: index `j ∈ {1, …, |S|}` reads `p(GetEltWithIndex(B, O, j))`, index `|S| + 1 + t` reads `π t`; `⊥` and
indices out of range read `0`. -/
def FlatVerifier.answers (V : FlatVerifier F) (B : List F) (O : F) (p : F → F) (π : Fin V.length → F)
    (r : List Bool) (i : ℕ) : F :=
  match V.Q r i with
  | none => 0
  | some j =>
    if 1 ≤ j ∧ j ≤ 2 ^ B.length then p (eltWithIndex B O j)
    else if h : j - 2 ^ B.length - 1 < V.length ∧ 2 ^ B.length < j then π ⟨j - 2 ^ B.length - 1, h.1⟩
    else 0

/-- `V^{(p,π)}(x; r)`. -/
def FlatVerifier.accepts (V : FlatVerifier F) (B : List F) (O : F) (p : F → F) (π : Fin V.length → F)
    (r : Fin V.rand → Bool) : Bool :=
  V.D (List.ofFn r) (V.answers B O p π (List.ofFn r))

/-- `Pr_R[V^{(p,π)}(x; R) = 1]` for uniform `R ∈ {0,1}^rand`. -/
noncomputable def FlatVerifier.acceptProb (V : FlatVerifier F) (B : List F) (O : F) (p : F → F)
    (π : Fin V.length → F) : ℝ :=
  ((univ.filter fun r => V.accepts B O p π r = true).card : ℝ) / (2 : ℝ) ^ V.rand

end Verifiers

/-! ## The published statements -/

/-- **BCGT13 Theorem 11.1 with Def 4.15** (p.51; p.20). "Theorem 11.1. The (strong) PCPP verifiers V_RS
and V_VRS have respective soundness functions s_RS(δ, n) ≥ δ/(1 + (2^{η+1} + κ^{log c})/(1 − 2^{−η})) and
s_VRS(δ, n) ≥ δ/(2 + (2^{η+1} + κ^{log c})/(1 − 2^{−η})), where n = 2^κ, (η, κ0, γ, μ) are any integers
satisfying [Eq. (6)]". Def 4.15: "1. (Perfect) Completeness: If (x, y) ∈ L then there exists π such that
Pr_R[V_L^{(y,π)}(x; R) = 1] = 1. 2. Soundness: For every π it holds that Pr_R[V_L^{(y,π)}(x; R) = 1] ≤ 1 −
s(Δ(y, L_x), n)." Soundness is stated in the equivalent "far" form (the codes are nonempty and finite on `S`).
The far form quantifies over every real `δ`, including `δ ≤ 0`; it is a logical reformulation of Def 4.15(2), not
an extra source claim: for `δ > 0` the hypothesis gives `δ ≤ Δ(p, code)` and the printed `s` is increasing in `δ`;
for `δ ≤ 0` the bound `1 − δ/(positive denominator) ≥ 1` holds for every acceptance probability.
Range of `d`: the top-level `V_RS` clause is claimed only for `d ≥ 1`, as
Algorithm 13 ("d, positive integer", p.119) and §12.3.4 ("d is a positive integer", p.82) state; the
`V_VRS` clause keeps its printed range `2^{|B_H|} ≤ d < 2^{|B|}` (its internal degree-`(d − |H|)` call to `V_RS` is part
of Algorithm 12 itself, not a separate top-level claim). -/
def BCGT13_Theorem11_1 : Prop :=
  ∀ T : Tuple, T.Valid → T.PositiveExponents →
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (ℓ : ℕ), Fintype.card F = 2 ^ ℓ →
  ∀ (B : List F) (O : F), IsBasis B O →
    -- V_RS on explicit input (I_ℓ, B_S, O_S, d), "d, positive integer indicating what “low-degree” means"
    -- (Algorithm 13 inputs, p.119; §12.3.4, p.82: "… and d is a positive integer")
    (∀ d : ℕ, 1 ≤ d → d < 2 ^ B.length →
      (∀ p ∈ RS (span B O) d, ∃ π, ∀ r, (vRS T B O d).accepts B O p π r = true) ∧
      ∀ (p : F → F) (π : Fin (vRS T B O d).length → F) (δ : ℝ),
        (∀ q ∈ RS (span B O) d, δ ≤ fracDist (span B O) p q) →
        (vRS T B O d).acceptProb B O p π ≤ 1 - δ / (1 + soundTerm T.η T.κ0 T.γ T.μ B.length)) ∧
    -- V_VRS on explicit input (I_ℓ, B_S, O_S, B_H, O_H, d)
    (∀ (BH : List F) (OH : F), IsBasis BH OH → span BH OH ⊆ span B O →
     ∀ d : ℕ, 2 ^ BH.length ≤ d → d < 2 ^ B.length →
      (∀ p ∈ VRS (span B O) (span BH OH) d, ∃ π, ∀ r, (vVRS T B O BH OH d).accepts B O p π r = true) ∧
      ∀ (p : F → F) (π : Fin (vVRS T B O BH OH d).length → F) (δ : ℝ),
        (∀ q ∈ VRS (span B O) (span BH OH) d, δ ≤ fracDist (span B O) p q) →
        (vVRS T B O BH OH d).acceptProb B O p π ≤ 1 - δ / (2 + soundTerm T.η T.κ0 T.γ T.μ B.length))

end NearCubicGates.Published.BCGT13

end

/-! ## 12. CW19 Lemma 26: the source linear code

1. Bibliography: L. Chen and R. R. Williams, *Stronger Connections Between
   Circuit Analysis and Circuit Lower Bounds, via PCPs of Proximity*,
   34th Computational Complexity Conference (CCC 2019), LIPIcs 137,
   article 19, pp. 19:1--19:43. Section 2.4, Lemma 26, printed p. 19:16.
   Source PDF SHA256:
   `c3c6ea6f80dbdf92a1887272fc2d618a4f63bd887d1cc1186dcf299a3aa99533`.
2. Quoted statement: "There is a constant δ > 0 such that there is a
   constant-rate linear error correcting code ECC with minimum relative
   distance δ, an efficient encoder Enc and an efficient decoder Dec
   recovering error up to c1 · δ, where c1 is a universal constant."
3. Quantifiers: one family, one positive distance, one positive decoding
   fraction, one onset and one rate constant are fixed simultaneously.
   The two ordinary programs and their polynomial constants are fixed for
   that family; neither program depends on a message or a received word.
4. The source guarantees decoding only near a codeword. Both termination
   and correctness below are required only under that promise. No behavior
   outside the promise is asserted. Constant rate is stated beyond an onset.
5. Conventions: vectors are Boolean functions on `Fin`; linearity over F₂ is
   preservation of zero and pointwise XOR. Hamming distance is the fraction
   of unequal coordinates. The encoder reads the message bits. The decoder
   reads a unary message length, a separator and the received word. Programs
   use a deterministic bit-multitape model, with polynomial costs measured
   in the lengths of these source encodings. The surrounding input frame,
   fresh output tape and exact physical output length, including trailing
   zero bits, are representation conventions rather than words attributed
   to Lemma 26. Conversion from other input encodings requires a proof.
6. The sparse-support binary-code construction uses this statement.
   The source radius is decreased if needed to use a closed promised radius;
   the later construction's radius, sparsity, totalization and finite-length
   patches are separate results. Three-block sparsity, parity supports and
   TM2 realizations are not asserted here. In particular, Lemma 27 is not assumed.
-/

section

set_option autoImplicit false

namespace NearCubicGates.Published.CW19Code

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.LocalBitMultitape
open NearCubicGates.PublishedSources.PCPP

/-- "a constant-rate linear error correcting code ECC" (Lemma 26).
The underlying code family, before any source properties are imposed. -/
structure BinaryFamily where
  length : ℕ → ℕ
  encode : (n : ℕ) → BitInput n → BitInput (length n)

/-- "linear error correcting code ECC" (Lemma 26).
The two vector-space identities for a binary linear map. -/
def IsLinear (F : BinaryFamily) : Prop :=
  (∀ n, F.encode n (fun _ => false) = fun _ => false) ∧
  ∀ n (x y : BitInput n),
    F.encode n (fun i => xor (x i) (y i)) =
      fun j => xor (F.encode n x j) (F.encode n y j)

/-- "minimum relative distance δ" (Lemma 26). -/
def MinimumDistance (F : BinaryFamily) (onset : ℕ) (distance : ℝ) : Prop :=
  ∀ n, onset ≤ n → ∀ x y : BitInput n, x ≠ y →
    distance ≤ relativeHamming (F.encode n x) (F.encode n y)

/-- Unary source description of the decoder's message length and received word.
This is a representation convention, not an additional published claim. -/
def decoderInput (F : BinaryFamily) (n : ℕ) (y : BitInput (F.length n)) : List Bool :=
  List.replicate n true ++ false :: List.ofFn y

/-- "an efficient encoder Enc" (Lemma 26).
An ordinary program, with one polynomial bound for all source lengths. -/
structure EfficientEncoder (F : BinaryFamily) (onset : ℕ) where
  program : Program
  coefficient : ℕ
  exponent : ℕ
  encodes : ∀ n, onset ≤ n → ∀ x : BitInput n, ∃ receipt,
    run program.machine (coefficient * (n + 1) ^ exponent)
      (program.inputTapes (List.ofFn x)) = some receipt ∧
    receipt.final.tapes program.outputTape = List.ofFn (F.encode n x)

/-- "an efficient decoder Dec recovering error up to c1 · δ" (Lemma 26).
This promised-time program has no asserted behavior on unpromised inputs. -/
structure PromisedDecoder (F : BinaryFamily) (onset : ℕ) (radius : ℝ) where
  program : Program
  coefficient : ℕ
  exponent : ℕ
  decodes : ∀ n, onset ≤ n → ∀ (x : BitInput n) (y : BitInput (F.length n)),
    relativeHamming (F.encode n x) y ≤ radius → ∃ receipt,
      run program.machine (coefficient * (n + F.length n + 1) ^ exponent)
        (program.inputTapes (decoderInput F n y)) = some receipt ∧
      receipt.final.tapes program.outputTape = List.ofFn x

/-- "There is a constant δ > 0 such that there is a constant-rate linear
error correcting code ECC with minimum relative distance δ, an efficient encoder Enc and an
efficient decoder Dec recovering error up to c1 · δ, where c1 is a universal constant."

Literal source ingredients only; the three-block construction of Lemma 27 is
deliberately absent. All constants and programs are independent of the input. -/
def Lemma26 : Prop :=
  ∃ (F : BinaryFamily) (distance fraction : ℝ) (onset rate : ℕ),
    0 < distance ∧ 0 < fraction ∧
    IsLinear F ∧
    (∀ n, onset ≤ n → F.length n ≤ rate * n) ∧
    MinimumDistance F onset distance ∧
    Nonempty (EfficientEncoder F onset) ∧
    Nonempty (PromisedDecoder F onset (fraction * distance))

end NearCubicGates.Published.CW19Code

end

/-! ## 13. Published statements: CW19Proximity

Lijie Chen and R. Ryan Williams, “Stronger Connections Between Circuit Analysis
and Circuit Lower Bounds, via PCPs of Proximity”, 34th Computational Complexity
Conference (CCC 2019), LIPIcs 137, article 19, pp. 19:1–19:43.
Definition 20 and Lemma 22: p. 19:15. Nonadaptive query and decision procedures:
Appendix A, pp. 19:38–19:39. DOI: 10.4230/LIPIcs.CCC.2019.19.
Source PDF SHA256: c3c6ea6f80dbdf92a1887272fc2d618a4f63bd887d1cc1186dcf299a3aa99533.
Text transcription SHA256: 86c5d90438e8a829e06d32030a620b63d60f6cee9e2454f916ae01f50c137073.

Lemma 22 is stated at soundness 1/2. For each fixed rational eta in (0,1), the
existential choices are a constant query bound, a verifier family, finite proof
lengths, a logarithmic randomness constant, algorithms and their polynomial
constants, and an honest proof family. These choices precede the universal
circuit and oracle quantifiers. No polynomial proof-length bound is assumed.

Binary coins are indexed by Fin (2 ^ randomBits). Input and proof coordinates
are separate, and a finite proof has value false outside its domain. CW19 does
not specify a machine alphabet or bit encoding. The flat topological circuit
words, framed request tuples, separate output tape and deterministic multitape
WordFunction model are representation conventions for its polynomial-time
algorithms. Physical input framing occupies 2|word|+1 cells, including trailing
zeros. Every polynomial budget charges the entire stated source request word.

This statement asserts no three-clause conversion, padding, dense addressing,
alternative circuit encoding, or Turing-machine simulation.
-/

section

set_option autoImplicit false

namespace NearCubicGates.Published.CW19Proximity

open NearCubicWires

/-- Section 2 (preliminaries): "when C is a general fan-in-2 circuit and w is a Boolean
input, (C, w) ∈ Circuit-Eval if and only if C(w) = 1." Input vertices count
toward size; the source description below is a flat topological node list. -/
structure SourceCircuit where
  arity : ℕ
  circuit : BooleanCircuit arity
  inputs_le_size : arity ≤ circuit.size

/-- Lemma 22: "poly(|C| + |w|) time." Representation convention for |C|:
three-bit node tags and self-delimited binary references in a flat node list. -/
def sourceNodeWord {n : ℕ} : BooleanNode n → List Bool
  | .const b => [false, false, false, b]
  | .input i => [false, false, true] ++ RepairOrdinary.frame i.val.bits
  | .not i => [false, true, false] ++ RepairOrdinary.frame i.bits
  | .and i j => [false, true, true] ++ RepairOrdinary.frame i.bits ++ RepairOrdinary.frame j.bits
  | .or i j => [true, false, false] ++ RepairOrdinary.frame i.bits ++ RepairOrdinary.frame j.bits

/-- Lemma 22: "poly(|C| + |w|) time." This explicit conventional source word
contains arity, node count, output index, then the flat node records. -/
def sourceCircuitWord (C : SourceCircuit) : List Bool :=
  RepairOrdinary.frame C.arity.bits ++
    RepairOrdinary.frame C.circuit.nodes.length.bits ++
    RepairOrdinary.frame C.circuit.output.val.bits ++
    C.circuit.nodes.flatMap sourceNodeWord

/-- Lemma 22: "can be constructed in poly(|C| + |w|) time." Ordinary
polynomial time means an actual finite-control bit-multitape computation on
the stated source words, with constants chosen after the proximity. -/
def SourcePolyTime {Request : Type} (input output : Request → List Bool) : Prop :=
  ∃ K e : ℕ, Nonempty (RepairOrdinary.WordFunction Request input output
    (fun request => K * ((input request).length + 1) ^ e))

/-- Definition 20: "V (x) tosses r(|x|) random coins, and makes at most q(|x|)
non-adaptive queries." Input and proof positions are kept separate. -/
abbrev QueryAddress (n : ℕ) := Fin n ⊕ ℕ

/-- Definition 20: "accepts oracle y ◦ π". -/
def oracleValue {n : ℕ} (input : BitInput n) (proof : ℕ → Bool)
    (address : QueryAddress n) : Bool :=
  Sum.elim input proof address

/-- Appendix A: "computes a predicate P = P (C, R) on these bits, and outputs
P (zk1 , zk2 , . . . , zkq )." The maps see coins but no oracle answers. -/
structure NonadaptiveVerifier (n q : ℕ) where
  randomBits : ℕ
  queryCount : Fin (2 ^ randomBits) → ℕ
  queryCount_le : ∀ coins, queryCount coins ≤ q
  query : (coins : Fin (2 ^ randomBits)) → Fin (queryCount coins) → QueryAddress n
  decision : (coins : Fin (2 ^ randomBits)) → BitInput (queryCount coins) → Bool

/-- Appendix A: "outputs P (zk1 , zk2 , . . . , zkq )." -/
def NonadaptiveVerifier.accepts {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool) (coins : Fin (2 ^ V.randomBits)) : Bool :=
  V.decision coins (fun j => oracleValue input proof (V.query coins j))

/-- Definition 20: "accepts oracle y ◦ π with probability at most s(|x|)." -/
noncomputable def NonadaptiveVerifier.fraction {n q : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : ℕ → Bool) : ℝ :=
  ((Finset.univ.filter fun coins => V.accepts input proof coins = true).card : ℝ) /
    (2 ^ V.randomBits : ℝ)

/-- Definition 20: "there is a proof π". A finite proof has zero values
outside its domain; every queried address is required to lie in its domain. -/
def finiteProofOracle {length : ℕ} (proof : BitInput length) : ℕ → Bool :=
  fun address => if h : address < length then proof ⟨address, h⟩ else false

/-- Definition 20: "non-adaptive queries." The bit tag separates input from
proof addresses; both addresses use ordinary self-delimited binary notation. -/
def queryAddressWord {n : ℕ} : QueryAddress n → List Bool
  | .inl i => false :: RepairOrdinary.frame i.val.bits
  | .inr address => true :: RepairOrdinary.frame address.bits

/-- Definition 20: "V (x) tosses r(|x|) random coins". -/
abbrev CoinRequest {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) :=
  Σ C : SourceCircuit, Fin (2 ^ (V C).randomBits)

/-- Definition 20: "makes at most q(|x|) non-adaptive queries". The source
query procedure reports its actual query count before any oracle answers. -/
def coinRequestWord {q : ℕ} {V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q}
    (p : CoinRequest V) : List Bool :=
  sourceCircuitWord p.1 ++ RepairOrdinary.frame p.2.val.bits

/-- Appendix A: "positions k1 = k1 (C, R), k2 = k2 (C, R), ...". -/
abbrev QueryRequest {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) :=
  Σ C : SourceCircuit, Σ coins : Fin (2 ^ (V C).randomBits), Fin ((V C).queryCount coins)

/-- Appendix A: "positions k1 = k1 (C, R), k2 = k2 (C, R), ...".
The input promise only restricts the supplied coin and query indices. -/
def queryRequestWord {q : ℕ} {V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q}
    (p : QueryRequest V) : List Bool :=
  sourceCircuitWord p.1 ++ RepairOrdinary.frame p.2.1.val.bits ++
    RepairOrdinary.frame p.2.2.val.bits

/-- Appendix A: "computes a predicate P = P (C, R) on these bits". -/
abbrev DecisionRequest {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) :=
  Σ C : SourceCircuit, Σ coins : Fin (2 ^ (V C).randomBits), BitInput ((V C).queryCount coins)

/-- Appendix A: "computes a predicate P = P (C, R) on these bits". -/
def decisionRequestWord {q : ℕ} {V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q}
    (p : DecisionRequest V) : List Bool :=
  sourceCircuitWord p.1 ++ RepairOrdinary.frame p.2.1.val.bits ++ List.ofFn p.2.2

/-- Lemma 22: "given the pair (C, w) ∈ Circuit-Eval". -/
abbrev AcceptedSourceInput := Σ C : SourceCircuit,
  {input : BitInput C.arity // C.circuit.eval input = true}

/-- Lemma 22: "given the pair (C, w) ∈ Circuit-Eval". This is a promise,
not an instruction for the honest algorithm to test circuit acceptance. -/
def acceptedSourceWord (p : AcceptedSourceInput) : List Bool :=
  sourceCircuitWord p.1 ++ List.ofFn p.2.val

/-- Source p.19:11: "hamming distance more than δn from all y that satisfy E". -/
def StrictlyFar (eta : ℚ) (C : SourceCircuit) (input : BitInput C.arity) : Prop :=
  ∀ accepted : BitInput C.arity, C.circuit.eval accepted = true →
    (eta : ℝ) < PublishedSources.PCPP.relativeHamming input accepted

/-- Lemma 22: "For any constants 0 < δ, s < 1, there is a PCP of
proximity system for Circuit-Eval with proximity δ, soundness s, number of
random bits r = O(log n) and query complexity q = O(1). Moreover, given the
pair (C, w) ∈ Circuit-Eval, a proof π making V (C) always accepts can be
constructed in poly(|C| + |w|) time."

Only the instance s=1/2 used in Appendix A is imported. Uniform query and
decision procedures are explicit. The finite proof length is unconstrained;
its polynomial trimmed replacement is proved, not assumed. `clog (L+2)` is
the total small-length convention for O(log L), with the constant existential. -/
def Lemma22Half : Prop :=
  ∀ eta : ℚ, 0 < eta → eta < 1 →
    ∃ q : ℕ, ∃ V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q,
    ∃ proofLength : SourceCircuit → ℕ,
      (∀ C coins j address, (V C).query coins j = .inr address → address < proofLength C) ∧
      (∃ a : ℕ, ∀ C, (V C).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord C).length + 2)) ∧
      SourcePolyTime sourceCircuitWord (fun C => (V C).randomBits.bits) ∧
      SourcePolyTime (coinRequestWord (V := V)) (fun p => ((V p.1).queryCount p.2).bits) ∧
      SourcePolyTime (queryRequestWord (V := V))
        (fun p => queryAddressWord ((V p.1).query p.2.1 p.2.2)) ∧
      SourcePolyTime (decisionRequestWord (V := V))
        (fun p => [(V p.1).decision p.2.1 p.2.2]) ∧
      (∀ C input, StrictlyFar eta C input → ∀ proof : BitInput (proofLength C),
        (V C).fraction input (finiteProofOracle proof) ≤ (1 / 2 : ℝ)) ∧
      ∃ honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1),
        (∀ p coins, (V p.1).accepts p.2.val (finiteProofOracle (honest p)) coins = true) ∧
        SourcePolyTime acceptedSourceWord (fun p => List.ofFn (honest p))

end NearCubicGates.Published.CW19Proximity

end

/-! ## 14. Published statement: STV Theorem 29 (list decoding of multivariate polynomials)

Leaf record:

1. **Locator.** M. Sudan, L. Trevisan, S. Vadhan, *Pseudorandom generators without the XOR lemma*, J. Comput.
   System Sci. 62(2):236–266 (2001). Read in the preprint of the journal version (24 pages; sha256 of the PDF
   `6155baab46b3204122e9f2f801a70f891b9333f34cf396b1047809973ce53cf7`; page numbers below are the preprint's), checked
   against ECCC report TR98-074, revision 2 (May 18, 2000; sha256 of the PDF
   `87ccd011e2e0d55929decddd29caaf4b4c89659dee9c93760a8e29d950d59865`). Places used: §4.1 Definition 20 (p. 13),
   §4.3 "the reconstruction problem" and **Theorem 29** (p. 17), whose proviso reads "provided ε > c√(d/|F|)" on the
   printed page.
2. **Proposition.** `NearCubicGates.Published.STV.Theorem29`, over the model `OracleMachine` (randomized oracle
   machines on the companion's multitape bit machines, `Statement.lean` §7) and the field representation
   `fieldElt` (bit vectors modulo an irreducible `q ∈ 𝔽₂[X]`).
3. **Quantifier ledger.** `∃ c L K e` (absolute: the constant `c` of the theorem, the constant of `O(1/ε)` and the
   coefficient and degree of `poly(m, d, log|F|, 1/ε)`) `∀ t q m d ε f ∃` list of machines. The list may depend on
   everything (it is the output of the reconstruction on oracle `f`); the machine that computes a given polynomial
   `p` is chosen after `p`.
4. **Source hypotheses.** `ε > c·√(d/|F|)` with `|F| = 2^t`. No other side condition (Theorem 29 states none).
5. **Conventions.**
   * Fields: only `F = 𝔽₂[X]/(q)` with `q` monic irreducible of degree `t` (`|F| = 2^t`, `log|F| = t`); an element
     is the `t`-bit word of its coefficients (`fieldElt`). This *specializes* "a field F" of the source to the binary
     fields the consumer uses, with the standard polynomial-basis representation in which field operations cost
     `poly(t)` (the running time `poly(m, d, log|F|, 1/ε)` presupposes such a representation).
   * "Oracle f : F^m → F": a function on words, `(Fin m → Fin t → Bool) → Fin t → Bool`.
   * "polynomial p : F^m → F of degree d": `P : MvPolynomial (Fin m) F` with `P.totalDegree ≤ d`, evaluated at the
     point the words denote. "(relative) agreement ε": `p(x) = f(x)` on at least an `ε` fraction of the `2^(t·m)`
     points (at least, as in the use on p. 15: "agree with f on at least an ε + 1/|F| fraction of the places").
   * "randomized oracle machine": `OracleMachine` below — a multitape bit machine (`Machine`) with five designated
     tapes (input, random, query, answer, output) and query states. On entering a query state the oracle's answer
     to the query tape's first `m·t` cells is written on the answer tape. The coins are the `randomBits` cells of
     the random tape, uniform. "M^f computes p" is Definition 20 at every point: `Pr_r[M^f(x) = p(x)] ≥ 3/4`.
   * "running time at most poly(...)": on every point and every coin string, the machine with oracle `f` halts
     within that many transitions. The machine's *description* (its `stateCount · 2^tapeCount` table entries) and
     its number of coins are bounded by the same polynomial: the machines are outputs of the reconstruction
     procedure, which runs in that time, so their descriptions have at most that length (and a machine running
     `T` steps reads at most `T` coins). Without a bound on the description the conclusion would be trivial
     (hard-wire `p`).
   * `O(1/ε)`: at most `L/ε` machines.
6. **Consumer.** The adapters of input 8 (namespace `NearCubicGates.Adapters.Amplification`): Lemma 28's
   concatenated decoding and Theorem 24's reconstruction in the target circuit model, proving
   `NearCubicGates.Close.CLW20_Lemma3_9_Multitape`.

**What is NOT claimed.** The uniformity of the reconstruction procedure (it is randomized and runs in time
`poly(m, d, log|F|, 1/ε)`; only the *existence* of its output list is stated, which follows since it succeeds with
probability `≥ 3/4 > 0`); fields other than `𝔽₂[X]/(q)`; Theorem 31's combinatorial list bound; anything about
Lemmas 25, 27, 28 or Theorem 24 (their analogues are proved in the adapters).
-/

section

set_option autoImplicit false

namespace NearCubicGates.Published.STV

open NearCubicWires.LocalBitMultitape Polynomial

/-! ## Field elements as bit words -/

/-- The polynomial `Σ_{w_i = 1} X^i` of a `t`-bit word. -/
noncomputable def wordPoly {t : ℕ} (w : Fin t → Bool) : (ZMod 2)[X] :=
  ∑ i : Fin t, if w i then (X : (ZMod 2)[X]) ^ (i : ℕ) else 0

/-- The element of `F = 𝔽₂[X]/(q)` denoted by a `t`-bit word (polynomial-basis representation). -/
noncomputable def fieldElt (q : (ZMod 2)[X]) {t : ℕ} (w : Fin t → Bool) : AdjoinRoot q :=
  AdjoinRoot.mk q (wordPoly w)

/-- The value of `P` at the point of `F^m` denoted by the words `x`. -/
noncomputable def evalAt (q : (ZMod 2)[X]) {m t : ℕ} (P : MvPolynomial (Fin m) (AdjoinRoot q))
    (x : Fin m → Fin t → Bool) : AdjoinRoot q :=
  MvPolynomial.eval (fun i => fieldElt q (x i)) P

/-- A point of `F^m` written on a tape: the `m` words of `t` bits, one after the other. -/
def pointWord {m t : ℕ} (x : Fin m → Fin t → Bool) : List Bool :=
  (List.ofFn fun i : Fin m => List.ofFn (x i)).flatten

/-- The point named by the first `m·t` cells of a tape (cells beyond the written part read as `false`). -/
def queryPoint (m t : ℕ) (tape : List Bool) : Fin m → Fin t → Bool :=
  fun i j => readTapeBit tape (i.val * t + j.val)

/-- The oracle `f : F^m → F` as an answer map on query-tape contents. -/
def fieldOracle {m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool) : List Bool → List Bool :=
  fun tape => List.ofFn (f (queryPoint m t tape))

/-! ## Randomized oracle machines (STV §4.1) -/

/-- A randomized oracle machine: a multitape bit machine with five designated tapes — `0` input, `1` coins,
`2` query, `3` answer, `4` output — query states `asks`, and `randomBits` coins. -/
structure OracleMachine where
  tapeCount : ℕ
  stateCount : ℕ
  fiveTapes : 5 ≤ tapeCount
  machine : Machine tapeCount stateCount
  asks : Fin stateCount → Bool
  randomBits : ℕ

namespace OracleMachine

variable (M : OracleMachine)

def queryTape : Fin M.tapeCount := ⟨2, by have := M.fiveTapes; omega⟩
def answerTape : Fin M.tapeCount := ⟨3, by have := M.fiveTapes; omega⟩
def outputTape : Fin M.tapeCount := ⟨4, by have := M.fiveTapes; omega⟩

/-- One transition with oracle `O`: the machine's own step; if it enters a query state, the answer to the
query tape replaces the answer tape, whose head returns to cell `0`. -/
def oracleStep (O : List Bool → List Bool) (c : Configuration M.tapeCount M.stateCount) :
    Option (Configuration M.tapeCount M.stateCount) :=
  (step M.machine c).map fun c' =>
    if M.asks c'.control then
      { control := c'.control
        heads := Function.update c'.heads M.answerTape 0
        tapes := Function.update c'.tapes M.answerTape (O (c'.tapes M.queryTape)) }
    else c'

/-- Run with oracle `O` for at most `fuel` transitions; `some` the halting configuration. -/
def oracleRun (O : List Bool → List Bool) :
    ℕ → Configuration M.tapeCount M.stateCount → Option (Configuration M.tapeCount M.stateCount)
  | 0, c => if M.machine.halted c.control then some c else none
  | fuel + 1, c =>
      if M.machine.halted c.control then some c
      else
        match M.oracleStep O c with
        | none => none
        | some c' => oracleRun O fuel c'

/-- The start: the input word on tape `0`, the coins on tape `1`, every other tape empty, heads at `0`. -/
def initial (input coins : List Bool) : Configuration M.tapeCount M.stateCount where
  control := M.machine.start
  heads := fun _ => 0
  tapes := fun i => if i.val = 0 then input else if i.val = 1 then coins else []

/-- The `t`-bit output word: the first `t` cells of the output tape. -/
def outputWord (t : ℕ) (c : Configuration M.tapeCount M.stateCount) : Fin t → Bool :=
  fun j => readTapeBit (c.tapes M.outputTape) j.val

/-- On point `x` with coins `r` and oracle `f`, the machine halts with an output denoting `v`. -/
def OutputsValue (q : (ZMod 2)[X]) {m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool)
    (x : Fin m → Fin t → Bool) (r : Fin M.randomBits → Bool) (v : AdjoinRoot q) : Prop :=
  ∃ fuel c, M.oracleRun (fieldOracle f) fuel (M.initial (pointWord x) (List.ofFn r)) = some c ∧
    fieldElt q (M.outputWord t c) = v

/-- STV Definition 20 (§4.1, p. 13): "A randomized procedure A is said to compute a function f : X → Y at a
point x ∈ X if Pr[A(x) = f(x)] ≥ 3/4, where the probability is taken over the internal coin tosses of A. … We
say that A computes f if it has agreement 1 with f."

`M^f` computes the polynomial function `P` (at every point, over the uniform coins). -/
def Computes (q : (ZMod 2)[X]) {m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool)
    (P : MvPolynomial (Fin m) (AdjoinRoot q)) : Prop :=
  ∀ x : Fin m → Fin t → Bool,
    3 * 2 ^ M.randomBits ≤ 4 * {r : Fin M.randomBits → Bool | M.OutputsValue q f x r (evalAt q P x)}.ncard

/-- "running time at most T": with oracle `f`, on every point and every coin string, the machine halts within
`T` transitions. -/
def HaltsWithin {m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool) (T : ℝ) : Prop :=
  ∀ (x : Fin m → Fin t → Bool) (r : Fin M.randomBits → Bool), ∃ fuel : ℕ, (fuel : ℝ) ≤ T ∧
    (M.oracleRun (fieldOracle f) fuel (M.initial (pointWord x) (List.ofFn r))).isSome

end OracleMachine

/-- "p has (relative) agreement ε with f": `p(x) = f(x)` on at least an `ε` fraction of `F^m`. -/
def Agrees (q : (ZMod 2)[X]) {m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool)
    (P : MvPolynomial (Fin m) (AdjoinRoot q)) (ε : ℝ) : Prop :=
  ε * 2 ^ (m * t) ≤ ({x : Fin m → Fin t → Bool | fieldElt q (f x) = evalAt q P x}.ncard : ℝ)

/-- **STV Theorem 29** (§4.3, p. 17):

"Recall that we wish to solve the following problem:
Given: An oracle f : F^m → F and parameters d ∈ ℕ and ε ∈ ℝ.
Goal: Reconstruct (an implicit representation for) every polynomial of total degree at most d that has
ε-agreement with the function f. Specifically, construct randomized oracle machines M1, …, Ml such that for every
polynomial p : F^m → F of degree d that has (relative) agreement ε with f, there exists j ∈ [l] such that M_j^f
computes p. …
Theorem 29 There exists a constant c such that the reconstruction problem above can be solved in time
poly(m, d, log|F|, 1/ε), provided ε > c√(d/|F|). Furthermore, the reconstruction algorithm produces a list of at
most l = O(1/ε) oracle machines, each with running time at most poly(m, d, log|F|, 1/ε)."

Stated for `F = 𝔽₂[X]/(q)` (`|F| = 2^t`), as the existence of the reconstruction's output list (see the record
above). -/
def Theorem29 : Prop :=
  ∃ (c L K : ℝ) (e : ℕ), 0 < c ∧
    ∀ (t : ℕ) (q : (ZMod 2)[X]), q.Monic → Irreducible q → q.natDegree = t →
    ∀ (m d : ℕ) (ε : ℝ), c * Real.sqrt ((d : ℝ) / 2 ^ t) < ε →
    ∀ f : (Fin m → Fin t → Bool) → Fin t → Bool,
    ∃ Ms : List OracleMachine,
      (Ms.length : ℝ) ≤ L / ε ∧
      (∀ M ∈ Ms,
        ((M.stateCount * 2 ^ M.tapeCount : ℕ) : ℝ) ≤ K * ((m : ℝ) + d + t + 1 / ε) ^ e ∧
        (M.randomBits : ℝ) ≤ K * ((m : ℝ) + d + t + 1 / ε) ^ e ∧
        M.HaltsWithin f (K * ((m : ℝ) + d + t + 1 / ε) ^ e)) ∧
      ∀ P : MvPolynomial (Fin m) (AdjoinRoot q), P.totalDegree ≤ d → Agrees q f P ε →
        ∃ M ∈ Ms, M.Computes q f P

end NearCubicGates.Published.STV

end

/-! ## 15. FindIrrPoly: deterministic polynomial-time irreducible polynomials over `F2` (published statement)

1. *Locator.* E. Ben-Sasson, A. Chiesa, D. Genkin, E. Tromer, "On the Concrete Efficiency of Probabilistically-
   Checkable Proofs", ECCC TR12-045 rev. 3, Algorithm 17 "FindIrrPoly" (p. 124), which cites V. Shoup, "New
   algorithms for finding irreducible polynomials over finite fields", FOCS 1988, Corollary 3.2. Source PDF:
   sha256 `9f16fb370af704e8a08429608ab93c1c4934d806661d0064bd881615cc4d7aa0`.
2. *Statement.* `FindIrrPolyAlgorithm17` below.
3. *Quantifier ledger.* One choice function `irrPoly` and one pair `K, e`, fixed before the degree `ℓ`.
4. *Hypotheses kept.* `ℓ ≥ 1` (there is no irreducible polynomial of degree `0`).
5. *Conventions.* "Runs in time `poly(ℓ)`" is the existence of an ordinary machine (`RepairOrdinary.WordFunction`)
   with budget `K·(ℓ+1)^e` on the printed input `1^ℓ`; the output `I_ℓ` is written as its `ℓ + 1` coefficients,
   constant term first (`coeffWord`, the natural encoding of a polynomial). The output's correctness is
   `IrreducibleChoice` below.
6. *Not claimed.* Any explicit exponent; anything at `ℓ = 0`; primitivity.
7. *Use.* The field of the succinct constraint-satisfaction instance in the short PCP is represented by the
   irreducible polynomial this algorithm outputs.
-/

section

set_option autoImplicit false

namespace NearCubicGates.Published.Shoup

noncomputable section

open Polynomial

/-- An irreducible-polynomial choice: for every `f ≥ 1`, an irreducible polynomial of degree `f` over `F2` (the
output `I_f` of `FindIrrPoly` on `1^f`, BCGT13 Algorithm 17). -/
def IrreducibleChoice (irrPoly : ℕ → (ZMod 2)[X]) : Prop :=
  ∀ f, 1 ≤ f → Irreducible (irrPoly f) ∧ (irrPoly f).natDegree = f

/-- The `f + 1` coefficients of a polynomial of degree `f`, constant term first (FindIrrPoly's output). -/
def coeffWord (f : ℕ) (a : (ZMod 2)[X]) : List Bool := List.ofFn fun i : Fin (f + 1) => decide (a.coeff i.val = 1)

/-- BCGT13 Algorithm 17's algorithm "runs in time poly(ℓ)", read at bit level: an
ordinary machine maps `1^f` (`f ≥ 1`) to the coefficients of `irrPoly f` within `K·(f+1)^e` steps. -/
def PolyTimeIrrChoice (irrPoly : ℕ → (ZMod 2)[X]) : Prop :=
  ∃ K e : ℕ, Nonempty (NearCubicWires.RepairOrdinary.WordFunction {f : ℕ // 1 ≤ f}
    (fun f => List.replicate f.val true) (fun f => coeffWord f.val (irrPoly f.val)) (fun f => K * (f.val + 1) ^ e))

/-- **BCGT13 Algorithm 17 (FindIrrPoly)**, as printed: "inputs: `1^ℓ`, desired degree presented in unary; output:
`I_ℓ`, irreducible polynomial of degree `ℓ` over `F2` with root `x`, inducing the field extension `F_{2^ℓ} := F2(x)`;
1. the algorithm of [Sho88, Corollary 3.2], which runs in time `poly(ℓ)`." -/
def FindIrrPolyAlgorithm17 : Prop :=
  ∃ irrPoly : ℕ → Polynomial (ZMod 2), IrreducibleChoice irrPoly ∧ PolyTimeIrrChoice irrPoly

end

end NearCubicGates.Published.Shoup

end

/-! ## 16. Published statement: Williams, JACM 2014, Corollary 4.4 (= Corollary C.2), in the multitape model

## Record of the transcription

1. **Source.** R. Williams, "Nonuniform ACC Circuit Lower Bounds", J. ACM 61(1), Article 2, 2014
   (doi 10.1145/2559903). Corollary 4.4 (printed p. 2:17) = Corollary C.2 (printed p. 2:29); the machine-model
   sentences are in §4 (printed p. 2:16) and Appendix C (printed p. 2:26). Source PDF (the ACM Digital Library
   version): sha256 `78d7c472224906600e31369914d4210d875af894b92903c362c3c1cf680b021c`.
   The PDF's text layer drops superscripts: "N .1" is `N^{.1}`, "N 2" is `N²`.
2. **Proposition.** `RectangularProductLeaf` below, over the model `MultitapeTM` defined in this file only
   (Mathlib only; no project definitions).
3. **Quantifier ledger.** One machine `M`, its input and output tapes, the constants `C`, `e` and the onset `N₀`
   are existential and chosen first; then `∀ N m` with `N₀ ≤ N` and `m = N^{1/10}`, then `∀ A B`. Nothing chosen
   later depends on nothing chosen earlier except as listed.
4. **Hypotheses of the source.** "For all sufficiently large N" (the onset `N₀`); dimensions `N × N^{.1}` and
   `N^{.1} × N`; 0-1 entries; product "over the integers"; time `O(N² · poly(log N))`, where Williams' notation
   (printed p. 2:6) is "poly(f(n)) to denote a growth rate of the form c f(n)^c for a constant c". No success
   probability (deterministic).
5. **Conventions (transcription choices; the source fixes none of them).** Williams prints no tape layout, alphabet
   or matrix encoding; he says only "(even on a multitape TM)". We read "multitape TM" as the textbook deterministic
   multitape machine: finite control, finitely many one-sided tapes over a finite alphabet with a blank, one
   transition per step that writes every scanned cell and moves every head one cell left, right or not at all
   (a left move on cell `0` stays), halting when no transition applies; time = number of steps.
   *Input:* on one input tape, the entries of `A` row by row as digit symbols, one separator, the entries of `B` row
   by row, then blanks; all other tapes blank, all heads on cell `0`. *Output:* on the output tape, for each entry of
   the product, row by row, its base-2 digits `Nat.digits 2` (least significant first; zero has no digits) followed
   by one separator, then blanks. *Dimension:* `N^{.1}` is the real power `(N:ℝ)^(1/10)`; a matrix dimension is a
   natural number, so the statement speaks exactly of the `N` for which `N^{.1}` is one (no rounding is chosen).
   *Logarithm:* base two here; changing a fixed logarithm base changes only the existential time constant.
   The conversions to the target statement's tapes (`LocalBitMultitape`, `natWord N` header, fixed-width output)
   are proved in `SourceAdapters/Williams/*`, not assumed here.
6. **What is NOT claimed.** Nothing below `N₀`; nothing about other encodings, alphabets or tape layouts; nothing about
   non-0-1 matrices or other fields; no space bound. **Consumer:** `SourceAdapters/Williams/*` proves
   `NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4` (the type of the field `rectangularProduct` of
   `NineInputs`).
-/

section

namespace NearCubicGates.Published.Williams

set_option autoImplicit false

/-! ## The textbook multitape machine -/

/-- The move of one head in one step. -/
inductive Move where
  | left
  | stay
  | right
deriving DecidableEq

/-- Head positions on a one-sided tape: a left move on cell `0` stays on cell `0`. -/
def Move.apply : Move → ℕ → ℕ
  | .left, h => h - 1
  | .stay, h => h
  | .right, h => h + 1

/-- A finite tape alphabet: `0` is the blank, `1` and `2` are the digits `0` and `1`, `3` is the separator, and the
`extra` further symbols are work symbols. -/
abbrev Symbol (extra : ℕ) := Fin (extra + 4)

namespace Symbol

/-- The blank. -/
def blank {extra : ℕ} : Symbol extra := 0

/-- The digit symbol of a bit. -/
def digit {extra : ℕ} (b : Bool) : Symbol extra := if b then 2 else 1

/-- The separator. -/
def separator {extra : ℕ} : Symbol extra := 3

end Symbol

/-- A deterministic multitape Turing machine: `tapes` one-sided tapes over `Symbol extraSymbols`, `states` control
states, a start state, and a partial transition function. A transition reads the scanned symbol of every tape and
gives the next state, the symbol written on every tape and the move of every head. -/
structure MultitapeTM where
  tapes : ℕ
  extraSymbols : ℕ
  states : ℕ
  start : Fin states
  transition : Fin states → (Fin tapes → Symbol extraSymbols) →
    Option (Fin states × (Fin tapes → Symbol extraSymbols) × (Fin tapes → Move))

namespace MultitapeTM

variable (M : MultitapeTM)

/-- A configuration: control state, head positions and tape contents (cell `p` of tape `i`). -/
structure Configuration where
  state : Fin M.states
  heads : Fin M.tapes → ℕ
  contents : Fin M.tapes → ℕ → Symbol M.extraSymbols

variable {M}

/-- The symbols under the heads. -/
def Configuration.scanned (c : M.Configuration) : Fin M.tapes → Symbol M.extraSymbols :=
  fun i => c.contents i (c.heads i)

variable (M)

/-- One step; `none` when no transition applies (the machine has halted). -/
def step (c : M.Configuration) : Option M.Configuration :=
  (M.transition c.state c.scanned).map fun a =>
    { state := a.1
      heads := fun i => (a.2.2 i).apply (c.heads i)
      contents := fun i => Function.update (c.contents i) (c.heads i) (a.2.1 i) }

/-- `M.run t c = some c'`: from `c`, the machine makes exactly `t` steps and is then in `c'`. -/
def run : ℕ → M.Configuration → Option M.Configuration
  | 0, c => some c
  | t + 1, c => (M.step c).bind (run t)

/-- The initial configuration on `input` written on tape `inputTape`: start state, every head on cell `0`, every
other cell blank. -/
def initial (inputTape : Fin M.tapes) (input : List (Symbol M.extraSymbols)) : M.Configuration where
  state := M.start
  heads := fun _ => 0
  contents := fun i p => if i = inputTape then input.getD p Symbol.blank else Symbol.blank

end MultitapeTM

/-! ## Matrices and their words -/

/-- The entries of a matrix row by row. -/
def rowMajor {α : Type} {n m : ℕ} (A : Fin n → Fin m → α) : List α :=
  (List.ofFn fun i => List.ofFn fun j => A i j).flatten

/-- "multiplied over the integers": `(A·B)(i,j) = Σ_l A(i,l)·B(l,j)` with the 0-1 entries read as the integers `0`,
`1`. All terms are nonnegative, so the value is a natural number. -/
def integerProduct {n m p : ℕ} (A : Fin n → Fin m → Bool) (B : Fin m → Fin p → Bool) : Fin n → Fin p → ℕ :=
  fun i j => ∑ l, (if A i l then 1 else 0) * (if B l j then 1 else 0)

/-- The input word: `A` row by row, a separator, `B` row by row. -/
def inputWord {extra n m p : ℕ} (A : Fin n → Fin m → Bool) (B : Fin m → Fin p → Bool) : List (Symbol extra) :=
  (rowMajor A).map Symbol.digit ++ Symbol.separator :: (rowMajor B).map Symbol.digit

/-- One natural number: its base-2 digits (least significant first) and a separator. -/
def numberWord {extra : ℕ} (x : ℕ) : List (Symbol extra) :=
  (Nat.digits 2 x).map (fun d => Symbol.digit (decide (d = 1))) ++ [Symbol.separator]

/-- The output word: the entries row by row, each as `numberWord`. -/
def outputWord {extra n p : ℕ} (P : Fin n → Fin p → ℕ) : List (Symbol extra) :=
  (rowMajor P).flatMap numberWord

/-! ## The published statement -/

/-- **Williams, JACM 2014, Corollary 4.4 (printed p. 2:17) = Corollary C.2 (printed p. 2:29), verbatim:**
"For all sufficiently large N, two 0-1 matrices of dimensions N × N^{.1} and N^{.1} × N can be multiplied over the
integers in O(N² · poly(log N)) time."
**Machine model (Appendix C, printed p. 2:26, verbatim):** "here we verify using standard ideas that Coppersmith's
algorithm can indeed be implemented to run (even on a multitape TM) in O(N² · poly(log N)) time, on matrices over
any field of poly(N) elements." **Uniformity (§4, printed p. 2:16, verbatim):** "Coppersmith's algorithm is
explicit, in that it can be executed on typical machine model (even a multitape TM) in O(N² · poly(log N)) time".

Read as: one multitape machine, constants `C`, `e` and an onset `N₀`, such that for every `N ≥ N₀` and every
natural `m` equal to `N^{.1}`, on every pair of 0-1 matrices of dimensions `N × m` and `m × N` the machine halts
within `C · N² · (log₂ N)^e` steps with their integer product on its output tape (conventions in the header). -/
def RectangularProductLeaf : Prop :=
  ∃ (M : MultitapeTM) (inputTape outputTape : Fin M.tapes) (C e N₀ : ℕ),
    ∀ (N m : ℕ), N₀ ≤ N → (m : ℝ) = (N : ℝ) ^ (1 / 10 : ℝ) →
    ∀ (A : Fin N → Fin m → Bool) (B : Fin m → Fin N → Bool),
      ∃ (t : ℕ) (c : M.Configuration),
        M.run t (M.initial inputTape (inputWord A B)) = some c ∧ M.step c = none ∧
        (t : ℝ) ≤ (C : ℝ) * (N : ℝ) ^ 2 * Real.logb 2 (N : ℝ) ^ e ∧
        c.contents outputTape = fun p => (outputWord (integerProduct A B)).getD p Symbol.blank

end NearCubicGates.Published.Williams

end

/-! ## 17. The published inputs and the final statement: `PublishedInputs`, `FinalStatement` -/

section

set_option autoImplicit false
namespace NearCubicGates.Close

/-- The published results the main theorem assumes: one field per published statement above. -/
structure PublishedInputs : Prop where
  apostol_primeNumberTheorem : NearCubicGates.Published.Apostol.primeNumberTheorem
  williams_rectangularProductLeaf : NearCubicGates.Published.Williams.RectangularProductLeaf
  bcgt13_theorem11_1 : NearCubicGates.Published.BCGT13.BCGT13_Theorem11_1
  shoup_findIrrPolyAlgorithm17 : NearCubicGates.Published.Shoup.FindIrrPolyAlgorithm17
  stv_theorem29 : NearCubicGates.Published.STV.Theorem29
  cw19Proximity_lemma22Half : NearCubicGates.Published.CW19Proximity.Lemma22Half
  cw19Code_lemma26 : NearCubicGates.Published.CW19Code.Lemma26

/-- The main theorem from the published results. -/
def FinalStatement : Prop := PublishedInputs → NearCubicGates.Target.MainStatement

end NearCubicGates.Close

end
