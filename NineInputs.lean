import Statement

/-!
# The nine inputs (not part of the statement)

`NineInputs`: the nine intermediate statements from which `main_from_inputs` (`MainTheorem.lean`) proves the
paper's main theorem, the definitions of their fields and the helper definitions those use, and
`NineFinalStatement := NineInputs → NearCubicGates.Target.MainStatement`. The trusted statement
(`Statement.lean`) does not use them: the proof derives every field of `NineInputs` from the published
statements of `PublishedInputs`. Nothing in this file is trusted.

## Contents

1. Balanced list codes
2. Binary codes of lists, Booleans and numbers
3. Boolean inputs and functions, real threshold gates, Boolean circuits
4. Matrices, literals, 3-CNF formulas, projected random bits and parity
5. Truth tables, circuit codes and amplifier requests
6. Row-major matrix encodings and fixed-width numbers
7. Framing, programs, word functions and verifiers
8. Ordinary programs, word functions, verifiers, hierarchies and weak machines; projection and literal codes
9. CNF formulas and their evaluation
10. Codes of machine actions and programs
11. Satisfiability of encoded CNF formulas
12. The SAT oracle on encoded formulas
13. Amplifier outputs and inputs
14. Number words
15. Input 1: threshold normalization (CTW26 Lemma 3.2)
16. Circuit size and approximation (used by input 8)
17. Circuits with a designated input (used by input 9)
18. The amplifier of input 8 (CLW20 Lemma 3.9)
19. Input 7: the refuter with an NP oracle (CLW20 Theorem 1.13)
20. Input 5: the rectangular matrix product (Williams 2014, Corollary 4.4)
21. Finite averages: `mean` (the uniform average used by input 3)
22. Input 4: the prime number theorem (Apostol)
23. Inputs 2 and 3: the central binomial restriction (CTW26 Appendix A.3) and the finite Bernstein bound (Vershynin, Theorem 2.8.4)
24. Input 9: the three-query PCPP and the linear code (CW19 Lemmas 24 and 27)
25. Input 6: the short PCP as an oracle circuit (Murray–Williams 2020)
26. Input 8 and the nine inputs: `NineInputs`, `NineFinalStatement`
-/

/-! ## 1. Balanced list codes -/

section

namespace NearCubicWires.CanonicalBinary

open NearCubicWires

def encodeBalancedList : List ℕ → ℕ
  | [] => 0
  | [value] => Nat.pair 1 value
  | first :: second :: rest =>
      let values := first :: second :: rest
      let leftLength := (values.length + 1) / 2
      let left := values.take leftLength
      let right := values.drop leftLength
      Nat.pair 2
        (Nat.pair (encodeBalancedList left) (encodeBalancedList right))
termination_by values => values.length
decreasing_by
  all_goals
    simp_wf
    have : ((rest.length + 2 + 1) / 2) ≤ rest.length + 1 := by omega
    simp
    omega

def decodeBalancedListAux : ℕ → ℕ → Option (List ℕ)
  | 0, code => if code = 0 then some [] else none
  | fuel + 1, code =>
      if code = 0 then
        some []
      else
        let outer := Nat.unpair code
        if outer.1 = 1 then
          some [outer.2]
        else if outer.1 = 2 then
          let branches := Nat.unpair outer.2
          match decodeBalancedListAux fuel branches.1,
              decodeBalancedListAux fuel branches.2 with
          | some left, some right => some (left ++ right)
          | _, _ => none
        else
          none

def decodeBalancedListCandidate (code : ℕ) : Option (List ℕ) :=
  decodeBalancedListAux (code + 1) code

def decodeBalancedList (code : ℕ) : Option (List ℕ) := do
  let values ← decodeBalancedListCandidate code
  if encodeBalancedList values = code then some values else none

end NearCubicWires.CanonicalBinary
end

/-! ## 2. Binary codes of lists, Booleans and numbers -/

section

namespace NearCubicWires.CanonicalBinary

open NearCubicWires

/-- A zero-terminated list whose cells expose both payload and tail through
two `unpair` instructions. -/
def encodeTaggedList : List ℕ → ℕ
  | [] => 0
  | value :: rest =>
      Nat.pair 1 (Nat.pair value (encodeTaggedList rest))

def boolCode (value : Bool) : ℕ := value.toNat

def encodeBoolList (values : List Bool) : ℕ :=
  encodeBalancedList (values.map boolCode)

def encodeBits (values : List Bool) : ℕ :=
  encodeBoolList values

/-- Canonical naturals are explicit little-endian bit lists, never raw machine
integers hidden behind `Encodable`. -/
def encodeNat (value : ℕ) : ℕ := encodeBits value.bits

end NearCubicWires.CanonicalBinary
end

/-! ## 3. Boolean inputs and functions, real threshold gates, Boolean circuits -/

section

open Finset
open scoped BigOperators

namespace NearCubicWires

/-- `L(n) = ⌈log₂(n+2)⌉`, computed exactly on naturals. -/
def logScale (n : ℕ) : ℕ := Nat.clog 2 (n + 2)

abbrev EncodedCNF := List (List (Bool × ℕ))

end NearCubicWires
end

/-! ## 4. Matrices, literals, 3-CNF formulas, projected random bits and parity -/

section

open Finset
open scoped BigOperators

namespace NearCubicWires.SourceInterfaces

open NearCubicWires

abbrev BitMatrix (rows columns : ℕ) := Fin rows → Fin columns → Bool

abbrev NatMatrix (rows columns : ℕ) := Fin rows → Fin columns → ℕ

inductive Literal (arity : ℕ) where
  | positive (index : Fin arity)
  | negative (index : Fin arity)

def Literal.eval {arity : ℕ} (literal : Literal arity)
    (assignment : BitInput arity) : Bool :=
  match literal with
  | .positive index => assignment index
  | .negative index => !(assignment index)

noncomputable def parityOn {n : ℕ} (support : Finset (Fin n))
    (input : BitInput n) : Bool :=
  support.toList.foldl (fun parity i => xor parity (input i)) false

end NearCubicWires.SourceInterfaces
end

/-! ## 5. Truth tables, circuit codes and amplifier requests -/

section

open Finset
open scoped BigOperators

namespace NearCubicWires.ExecutableInterfaces

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.SourceInterfaces

def boolFunctionTable {n : ℕ} (function : BoolFunction n) : List Bool :=
  (List.range (2 ^ n)).map fun code =>
    function fun index => code.testBit index.val

def encodeBooleanNode {n : ℕ} : BooleanNode n → ℕ
  | .const value =>
      encodeTaggedList [encodeNat 0, encodeNat value.toNat]
  | .input index =>
      encodeTaggedList [encodeNat 1, encodeNat index.val]
  | .not child =>
      encodeTaggedList [encodeNat 2, encodeNat child]
  | .and left right =>
      encodeTaggedList [encodeNat 3, encodeNat left, encodeNat right]
  | .or left right =>
      encodeTaggedList [encodeNat 4, encodeNat left, encodeNat right]

/-- Canonical DAG encoding: the topological node list is occurrence-sensitive,
and the distinguished output address is encoded separately. -/
def encodeBooleanCircuit {n : ℕ} (circuit : BooleanCircuit n) : ℕ :=
  encodeTaggedList
    [encodeBalancedList (circuit.nodes.map encodeBooleanNode),
      encodeNat circuit.output.val]

structure AmplifierRequest where
  inputArity : ℕ
  function : BoolFunction inputArity

end NearCubicWires.ExecutableInterfaces
end

/-! ## 6. Row-major matrix encodings and fixed-width numbers -/

section

namespace NearCubicWires.WilliamsProductCertificate

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces

/-- A matrix as a sequential row-major cell tape.  This is a `List` in the
logic, not a balanced codec and not a single machine register. -/
def rowMajorNatMatrix {rows columns : ℕ}
    (matrix : NatMatrix rows columns) : List ℕ :=
  (List.ofFn fun row => List.ofFn fun column => matrix row column).flatten

end NearCubicWires.WilliamsProductCertificate

namespace NearCubicWires.WilliamsLoaderForms

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.LocalBitMultitape
open NearCubicWires.SourceInterfaces
open NearCubicWires.WilliamsProductCertificate

def rowMajorBitMatrix {rows columns : ℕ}
    (matrix : BitMatrix rows columns) : List Bool :=
  (List.ofFn fun row => List.ofFn fun column => matrix row column).flatten

def fixedWidthNatBits (width value : ℕ) : List Bool :=
  List.ofFn fun bit : Fin width => value.testBit bit.val

def encodedNatCellTape (width : ℕ) (cells : List ℕ) : List Bool :=
  cells.flatMap (fixedWidthNatBits width)

end NearCubicWires.WilliamsLoaderForms

namespace NearCubicWires.WilliamsPublishedForm

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.LocalBitMultitape
open NearCubicWires.SourceInterfaces
open NearCubicWires.WilliamsProductCertificate
open NearCubicWires.WilliamsLoaderForms

def fixedWidthNatBits (width value : ℕ) : List Bool :=
  List.ofFn fun bit : Fin width => value.testBit bit.val

/-- A self-delimiting binary word.  Its length prefix makes concatenation of
the variable-width fields unambiguous. -/
def framedNatBits (value : ℕ) : List Bool :=
  List.replicate (natBitLength value) true ++
    false :: fixedWidthNatBits (natBitLength value) value

end NearCubicWires.WilliamsPublishedForm
end

/-! ## 7. Framing, programs, word functions and verifiers -/

section

namespace NearCubicWires.RepairOrdinary

open LocalBitMultitape SourceInterfaces

set_option autoImplicit false

def Verifier.accepts (v : Verifier) (input witness : List Bool) : Prop :=
  ∃ fuel, v.acceptsAt fuel input witness

/-- The language of `v` at witness length `witnessLength n`: the inputs for which some witness of that
    length is accepted. -/
def Verifier.language (v : Verifier) (witnessLength : ℕ → ℕ) :
    (n : ℕ) → BitInput n → Prop :=
  fun n x => ∃ w : BitInput (witnessLength n),
    v.accepts (List.ofFn x) (List.ofFn w)

end NearCubicWires.RepairOrdinary
end

/-! ## 8. Ordinary programs, word functions, verifiers, hierarchies and weak machines; projection and literal codes -/

section

namespace NearCubicWires.RepairSource

open SourceInterfaces LocalBitMultitape ExecutableInterfaces CanonicalBinary

set_option autoImplicit false

abbrev OrdinaryWordFunction := RepairOrdinary.WordFunction

structure OrdinaryHierarchy (T : ℕ → ℕ) where
  verifier : OrdinaryVerifier
  coefficient : ℕ
  coefficientPositive : 0 < coefficient
  halts : ∀ n (x : BitInput n) (w : BitInput (coefficient*(T n+1))),
    ∃ receipt, run verifier.machine (coefficient*(T n+1))
      (verifier.inputTapes (List.ofFn x) (List.ofFn w)) = some receipt

def OrdinaryHierarchy.time {T : ℕ → ℕ} (H : OrdinaryHierarchy T) (n : ℕ) : ℕ :=
  H.coefficient*(T n+1)

structure OrdinaryWeakMachine where
  verifier : OrdinaryVerifier
  runtime : ℕ → ℕ
  halts : ∀ n (x : BitInput n) (w : BitInput (n/16)),
    ∃ receipt, run verifier.machine (runtime n)
      (verifier.inputTapes (List.ofFn x) (List.ofFn w)) = some receipt

def OrdinaryWeakMachine.accepts (M : OrdinaryWeakMachine)
    (n : ℕ) (x : BitInput n) : Prop :=
  M.verifier.language (fun n => n/16) n x

def OrdinaryLittleO (M : OrdinaryWeakMachine) (T : ℕ → ℕ) : Prop :=
  ∀ multiplier : ℕ, 0 < multiplier →
    ∃ onset, ∀ n, onset ≤ n → multiplier*M.runtime n ≤ T n

def literalCode {t : ℕ} (l : Literal t) : ℕ :=
  match l with | .positive i => 2*i.val | .negative i => 2*i.val+1

abbrev InputRequest := Σ n : ℕ, BitInput n

end NearCubicWires.RepairSource
end

/-! ## 9. CNF formulas and their evaluation -/

section

namespace NearCubicWires.TseitinCNF

open NearCubicWires

abbrev EncodedLiteral := Bool × ℕ

abbrev EncodedClause := List EncodedLiteral

def literalEval (assignment : ℕ → Bool) (literal : EncodedLiteral) : Bool :=
  if literal.1 then assignment literal.2 else !(assignment literal.2)

def clauseEval (assignment : ℕ → Bool) (clause : EncodedClause) : Bool :=
  clause.any (literalEval assignment)

def formulaEval (assignment : ℕ → Bool) (formula : EncodedCNF) : Bool :=
  formula.all (clauseEval assignment)

end NearCubicWires.TseitinCNF
end

/-! ## 10. Codes of machine actions and programs -/

section

namespace NearCubicWires.RepairSource.VerifierEncoding

open SourceInterfaces ExecutableInterfaces LocalBitMultitape

set_option autoImplicit false

def fixedBits (width value : ℕ) : List Bool :=
  List.ofFn fun i : Fin width => value.testBit i.val

def writeCode : Option Bool → List Bool
  | none => [false, false]
  | some false => [true, false]
  | some true => [true, true]

def moveCode : HeadMove → List Bool
  | .left => [false, false]
  | .stay => [true, false]
  | .right => [false, true]

def actionCode {t s : ℕ} (width : ℕ) : Option (Action t s) → List Bool
  | none => false :: List.replicate (width + 4*t) false
  | some action => true :: (fixedBits width action.nextControl.val ++
      (List.ofFn fun i : Fin t => writeCode (action.write i) ++ moveCode (action.move i)).flatten)

def code (v : OrdinaryVerifier) : List Bool :=
  let width := natBitLength v.stateCount
  List.replicate v.tapeCount true ++ [false] ++
  List.replicate v.stateCount true ++ [false] ++
  fixedBits width v.machine.start.val ++
  (List.ofFn fun i : Fin v.stateCount => [v.machine.halted i, v.accepting i]).flatten ++
  (List.ofFn fun i : Fin v.stateCount =>
    (List.ofFn fun mask : Fin (2 ^ v.tapeCount) =>
      actionCode width (v.machine.rule i (fun tape => mask.val.testBit tape.val))).flatten).flatten

end NearCubicWires.RepairSource.VerifierEncoding
end

/-! ## 11. Satisfiability of encoded CNF formulas -/

section

namespace NearCubicWires.RepairSource.RecoveryOracle

set_option autoImplicit false

open TseitinCNF

noncomputable def mathSat (formula : EncodedCNF) : Bool := by
  classical
  exact decide (∃ assignment : Nat → Bool, formulaEval assignment formula = true)

end NearCubicWires.RepairSource.RecoveryOracle
end

/-! ## 12. The SAT oracle on encoded formulas -/

section

namespace NearCubicWires.RepairSource.RecoveryOracle

set_option autoImplicit false

open CanonicalBinary

def decodeSourceSAT (code : Nat) : Option EncodedCNF :=
  (decodeBalancedList code).map fun clauses =>
    clauses.map fun clauseCode =>
      (Encodable.decode (α := List (Bool × Nat)) clauseCode).getD []

noncomputable def sourceSAT (code : Nat) : Bool :=
  match decodeSourceSAT code with
  | some formula => formula.all (fun clause => clause.length = 3) && mathSat formula
  | none => false

end NearCubicWires.RepairSource.RecoveryOracle
end

/-! ## 13. Amplifier outputs and inputs -/

section

namespace NearCubicWires.RepairSource

open ExecutableInterfaces SourceInterfaces

set_option autoImplicit false

structure AmplifierOutput where
  arity : ℕ
  function : BoolFunction arity

/-- The outer ordinary carrier additionally frames this complete payload. -/
def amplifierInput (request : AmplifierRequest) : List Bool :=
  RepairOrdinary.frame request.inputArity.bits ++ boolFunctionTable request.function

end NearCubicWires.RepairSource
end

/-! ## 14. Number words -/

section

namespace NearCubicWires.RepairRepresentation

open SourceInterfaces ExecutableInterfaces RepairSource LocalBitMultitape CanonicalBinary
open WilliamsPublishedForm
open WilliamsProductCertificate
open scoped BigOperators

set_option autoImplicit false

def natWord (n : ℕ) : List Bool := framedNatBits n

end NearCubicWires.RepairRepresentation
end

/-! ## 15. Input 1: threshold normalization (CTW26 Lemma 3.2) -/

section

namespace NearCubicWires.Bindings.CTW26

open NearCubicWires NearCubicWires.SourceInterfaces
open scoped BigOperators

set_option autoImplicit false

/-- CTW26 §3, PDF p.9: "let I[α] be the indicator that α holds, i.e., it equals 1 if α holds
and 0 otherwise." -/
def I (α : Prop) [Decidable α] : ℕ := if α then 1 else 0

/-- CTW26 Definition 3.1, PDF p.9: "THR: This gate has parameters w1, w2, · · · , wm, t ∈ R". -/
structure THRGate (m : ℕ) where
  w : Fin m → ℝ
  t : ℝ

/-- CTW26 Definition 3.1, PDF p.9: the THR gate "outputs I[w1x1 + w2x2 + · · · + wmxm ≥ t]". -/
noncomputable def THRGate.output {m : ℕ} (g : THRGate m) (x : Fin m → ℝ) : ℕ :=
  I (∑ i, g.w i * x i ≥ g.t)

/-- CTW26 Definition 3.1, PDF p.9: "on input (x1, x2, · · · , xm) ∈ {0, 1}^m". -/
def IsInput {m : ℕ} (x : Fin m → ℝ) : Prop := ∀ i, x i = 0 ∨ x i = 1

/-- "an equivalent THR gate": the same output on every input in `{0,1}^m`. -/
def Equivalent {m : ℕ} (g h : THRGate m) : Prop :=
  ∀ x : Fin m → ℝ, IsInput x → g.output x = h.output x

/-- "an integer in range ±R": `p = k` for an integer `k` with `-R ≤ k ≤ R`. -/
def IsIntegerInRange (p : ℝ) (R : ℕ) : Prop :=
  ∃ k : ℤ, p = (k : ℝ) ∧ -(R : ℤ) ≤ k ∧ k ≤ (R : ℤ)

/-- **CTW26 Lemma 3.2 ([MTT61]), PDF page 10, verbatim:**
"For any THR gate on m input bits, there is an equivalent THR gate where all parameters are
integers in range ±m^m."

Every `m : ℕ` is quantified (no positivity; Lean's `0 ^ 0 = 1`). "All parameters" are the
weights `w i` and the threshold `t` of Definition 3.1. -/
def CTW26_Lemma3_2 : Prop :=
  ∀ (m : ℕ) (g : THRGate m), ∃ h : THRGate m,
    Equivalent g h ∧
      (∀ i, IsIntegerInRange (h.w i) (m ^ m)) ∧ IsIntegerInRange h.t (m ^ m)

end NearCubicWires.Bindings.CTW26
end

/-! ## 16. Circuit size and approximation (used by input 8) -/

section

namespace NearCubicWires.Bindings.CLW20Lemma39

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource
open NearCubicWires.LocalBitMultitape
open scoped BigOperators

set_option autoImplicit false

/-- "f ... has (general) circuits of size s": some circuit of size at most `s` computes `f`. -/
def HasCircuitOfSize {n : ℕ} (f : BoolFunction n) (s : ℕ) : Prop :=
  ∃ circuit : BooleanCircuit n, circuit.size ≤ s ∧ ∀ x, circuit.eval x = f x

/-- CLW20 PDF p.3: "cannot be (1/2 + ε)-approximated by circuits of type C, if every circuit from
C computes f correctly on less than (1/2 + ε)2^n of the n-bit inputs", with "circuits of size s"
read as size at most `s` (PDF p.17). -/
def CannotBeApproximated {m : ℕ} (g : BoolFunction m) (ε s : ℝ) : Prop :=
  ∀ circuit : BooleanCircuit m, (circuit.size : ℝ) ≤ s →
    ((Finset.univ.filter fun x => circuit.eval x = g x).card : ℝ) < (1 / 2 + ε) * 2 ^ m

end NearCubicWires.Bindings.CLW20Lemma39
end

/-! ## 17. Circuits with a designated input (used by input 9) -/

section

namespace NearCubicWires.Bindings.CLW20Lemma311

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.LocalBitMultitape
open scoped BigOperators

set_option autoImplicit false

/-- "a circuit D on n inputs of size m ≥ n". -/
structure Circuit where
  n : ℕ
  D : BooleanCircuit n
  sizeAtLeast : n ≤ D.size

/-- The size `m` of `D`: its number of nodes. -/
def Circuit.m (C : Circuit) : ℕ := C.D.size

/-- Tier 1: the circuit as a bit word, `n` and then the code of `D`. -/
def Circuit.word (C : Circuit) : List Bool :=
  natWord C.n ++ (encodeBooleanCircuit C.D).bits

end NearCubicWires.Bindings.CLW20Lemma311
end

/-! ## 18. The amplifier of input 8 (CLW20 Lemma 3.9) -/

section

namespace NearCubicWires.Bindings.CLW20Lemma39TM2

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource
open NearCubicWires.Bindings.CLW20Lemma39

set_option autoImplicit false

/-- The output word: the framed arity of `g`, then the full truth table of `g`. -/
def amplifierOutputWord (o : AmplifierOutput) : List Bool :=
  RepairOrdinary.frame o.arity.bits ++ boolFunctionTable o.function

/-- TIER 2 ALGORITHMIC CLAUSE. "given the 2^n-length truth table of f, the truth table of g can
be constructed in 2^{O(n)} time": a Mathlib `TM2ComputableInTime` machine from the truth table of
`f` (with its framed arity) to the truth table of `g` (with its framed arity), whose step bound
is at most `2^(timeExponent · n)` from the onset `timeOnset` on. -/
structure TruthTableConstructionTM2 (g : (n : ℕ) → BoolFunction n → AmplifierOutput) where
  machine : Turing.TM2ComputableInTime amplifierInput amplifierOutputWord
    (fun request : AmplifierRequest => g request.inputArity request.function)
  timeExponent : ℕ
  timeOnset : ℕ
  exponentialTime : ∀ request : AmplifierRequest, timeOnset ≤ request.inputArity →
    machine.time (amplifierInput request).length ≤ 2 ^ (timeExponent * request.inputArity)

/-- What the sentence asserts for one constant `c` and one time-constructible `S` (Tier 2). The
construction is a Mathlib TM2 machine. -/
structure Lemma3_9AtTM2 (c : ℝ) (S : ℕ → ℕ) where
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
  constructed in 2^{O(n)} time." (Tier 2: Mathlib's TM2 model.) -/
  construction : TruthTableConstructionTM2 g

end NearCubicWires.Bindings.CLW20Lemma39TM2
end

/-! ## 19. Input 7: the refuter with an NP oracle (CLW20 Theorem 1.13) -/

section

namespace NearCubicWires.Bindings.CLW20Theorem113

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.SourceInterfaces

set_option autoImplicit false

/-- "time-constructible" (standard notion, Tier 1 multitape model): a program that, given the word
`1^n`, outputs the binary digits of `T(n)` within `C·(T(n)+1)` steps. -/
def TimeConstructible (T : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, 0 < C ∧ Nonempty (OrdinaryWordFunction ℕ (fun n => List.replicate n true)
    (fun n => (T n).bits) (fun n => C * (T n + 1)))

/-- "n ≤ T(n) ≤ 2^{poly(n)}". -/
def InClockRange (T : ℕ → ℕ) : Prop :=
  (∀ n, n ≤ T n) ∧ ∃ C k : ℕ, ∀ n, T n ≤ 2 ^ (C * (n + 1) ^ k)

/-- "L ∈ NTIME[T(n)]" (nondeterministic `O(T(n))` time, Tier 1 multitape model): `L` is the
language of a verifier that halts within `c·(T(n)+1)` steps on every witness of length
`c·(T(n)+1)`. -/
def InNTIME (T : ℕ → ℕ) (L : Language) : Prop :=
  ∃ H : OrdinaryHierarchy T, ∀ n (x : BitInput n), L n x = true ↔ H.verifier.language H.time n x

/-- "The input to R is a pair (M, 1^n)": the framed description of `M`, then the framed `1^n`. -/
def pairInput (M : OrdinaryWeakMachine) (n : ℕ) : List Bool :=
  frame (VerifierEncoding.code M.verifier) ++ frame (List.replicate n true)

/-- `M(x)`, the truth value of "some witness makes `M` accept `x`" (CLW20 p.19). -/
noncomputable def machineValue (M : OrdinaryWeakMachine) (n : ℕ) (x : BitInput n) : Bool := by
  classical
  exact decide (M.accepts n x)

/-- The conclusion of Theorem 1.13 at one clock `T`: "there is a language L ∈ NTIME[T(n)] and an
algorithm R such that" items 1–3 hold. The degree `d` of "poly(T(n))" belongs to `R`. The
coefficient `C` and the onset of "every sufficiently large n" may depend on the fixed `M`. -/
def Theorem1_13At (T : ℕ → ℕ) : Prop :=
  ∃ L : Language, InNTIME T L ∧
    ∃ (R : OrdinaryOracleProgram) (d : ℕ),
      ∀ M : OrdinaryWeakMachine, OrdinaryLittleO M T →
        ∃ C onset : ℕ, ∀ n, onset ≤ n →
          ∃ x : BitInput n,
            OrdinaryOracleRuns RecoveryOracle.sourceSAT R (pairInput M n) (List.ofFn x)
              (C * (T n + 1) ^ d) ∧
            machineValue M n x ≠ L n x

/-- **CLW20 Theorem 1.13, PDF page 6 (printed p.5), verbatim:**
"Theorem 1.13 (Refuter with an NP Oracle, Informal). For every time-constructible function T(n)
such that n ≤ T(n) ≤ 2^{poly(n)}, there is a language L ∈ NTIME[T(n)] and an algorithm R such that:
1. Input. The input to R is a pair (M, 1^n), with the promise that M describes a nondeterministic
Turing machine running in o(T(n)) time and guessing at most n/10 bits.
2. Output. For every fixed M and every sufficiently large n, R(M, 1^n) outputs a string
x ∈ {0,1}^n such that M(x) ≠ L(x).
3. Complexity. R runs in poly(T(n)) time with adaptive access to an SAT oracle."
Each reading, including the multitape machine model, is listed in
`SourceMapping/7-refuter.md`. -/
def CLW20_Theorem1_13 : Prop :=
  ∀ T : ℕ → ℕ, TimeConstructible T → InClockRange T → Theorem1_13At T

end NearCubicWires.Bindings.CLW20Theorem113
end

/-! ## 20. Input 5: the rectangular matrix product (Williams 2014, Corollary 4.4) -/

section

namespace NearCubicWires.Bindings.Williams14

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.SourceInterfaces
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.WilliamsLoaderForms
open NearCubicWires.WilliamsProductCertificate
open scoped BigOperators

set_option autoImplicit false

/-- A 0-1 matrix entry as the integer `0` or `1`. -/
def bit (b : Bool) : ℕ := if b then 1 else 0

/-- "multiplied over the integers": `(A · B)(i, j) = Σ_l A(i, l) · B(l, j)`. -/
def product {n m p : ℕ} (A : BitMatrix n m) (B : BitMatrix m p) : NatMatrix n p :=
  fun i j => ∑ l, bit (A i l) * bit (B l j)

/-- Tier 1 input tapes: tape 0 = `N` in self-delimiting binary, then `A` row by row;
tape 1 = `B` row by row; every other tape blank. -/
def inputTapes {t m : ℕ} (N : ℕ) (A : BitMatrix N m) (B : BitMatrix m N) : Fin t → List Bool :=
  fun tape => if tape.val = 0 then natWord N ++ rowMajorBitMatrix A
    else if tape.val = 1 then rowMajorBitMatrix B else []

/-- Tier 1 output: the `N × N` product row by row, each entry in `⌊log₂ N⌋ + 1` binary digits
(least significant first). -/
def outputWord (N : ℕ) (P : NatMatrix N N) : List Bool :=
  encodedNatCellTape (natBitLength N) (rowMajorNatMatrix P)

/-- TIER 1 ALGORITHMIC CLAUSE (separable). One deterministic multitape machine (at least three
tapes; the output tape is neither input tape) that, for every `N = k^10 ≥ N₀` and every pair of
0-1 matrices of dimensions `N × N^{.1}` and `N^{.1} × N`, halts within `C · N² · (log₂ N)^e` steps
with their integer product on the output tape. -/
structure MultitapeMultiplier (N₀ C e : ℕ) where
  tapeCount : ℕ
  stateCount : ℕ
  threeTapes : 3 ≤ tapeCount
  machine : Machine tapeCount stateCount
  outputTape : Fin tapeCount
  outputFreshLeft : outputTape.val ≠ 0
  outputFreshRight : outputTape.val ≠ 1
  multiplies : ∀ (k : ℕ) (A : BitMatrix (k ^ 10) k) (B : BitMatrix k (k ^ 10)), N₀ ≤ k ^ 10 →
    ∃ receipt, run machine (C * (k ^ 10) ^ 2 * Nat.log 2 (k ^ 10) ^ e) (inputTapes (k ^ 10) A B) =
        some receipt ∧
      receipt.final.tapes outputTape = outputWord (k ^ 10) (product A B)

/-- **Williams, JACM 2014, Corollary 4.4 (PDF p.17) = Corollary C.2 (PDF p.29), verbatim:**
"For all sufficiently large N, two 0-1 matrices of dimensions N × N^{.1} and N^{.1} × N can be
multiplied over the integers in O(N² · poly(log N)) time."

Read with an onset `N₀` and constants `C`, `e`, all
existential, and one multitape machine (Tier 1) that is correct and within `C · N² · (log₂ N)^e`
for every `N = k^10 ≥ N₀`. -/
def Williams14_Corollary4_4 : Prop :=
  ∃ N₀ C e : ℕ, Nonempty (MultitapeMultiplier N₀ C e)

end NearCubicWires.Bindings.Williams14
end

/-! ## 21. Finite averages: `mean` (the uniform average used by input 3) -/

section

set_option autoImplicit false
namespace NearCubicGates.FiniteAverages
open scoped BigOperators

noncomputable def mean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card α

end NearCubicGates.FiniteAverages

end

/-! ## 22. Input 4: the prime number theorem (Apostol) -/

section

set_option autoImplicit false
namespace NearCubicGates.PublishedSources.PrimeDensity

/-- The prime number theorem at natural arguments: `|π(n) log n / n - 1| < ε` from an onset on, which may
depend on `ε`. -/
def ApostolPrimeNumberTheorem : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ onset : ℕ, 2 ≤ onset ∧
      ∀ n : ℕ, onset ≤ n →
        |(Nat.primeCounting n : ℝ) * Real.log (n : ℝ) / (n : ℝ) - 1| < epsilon

end NearCubicGates.PublishedSources.PrimeDensity

end

/-! ## 23. Inputs 2 and 3: the central binomial restriction (CTW26 Appendix A.3) and the finite Bernstein bound (Vershynin, Theorem 2.8.4) -/

section

set_option autoImplicit false
namespace NearCubicGates.PublishedSources.Witness
open scoped BigOperators
open NearCubicWires FiniteAverages

/-- Every k-subset occurs once, and every assignment on its complement occurs
once. Uniform averaging over this finite type is the published restriction law. -/
abbrev FiniteRestriction (n k : ℕ) :=
  Σ I : {I : Finset (Fin n) // I.card = k}, {i : Fin n // i ∉ I.val} → Bool

/-- The full input lies in the cell specified by the outer assignment. -/
def cellAgrees {n k : ℕ} (ρ : FiniteRestriction n k) (x : BitInput n) : Prop :=
  ∀ (i : Fin n) (hi : i ∉ ρ.1.val), x i = ρ.2 ⟨i, hi⟩

/-- The gate is not constant on the cell. -/
def gateLive {n k : ℕ} (g : RealThresholdGate n) (ρ : FiniteRestriction n k) : Prop :=
  ∃ x z : BitInput n, cellAgrees ρ x ∧ cellAgrees ρ z ∧ g.eval x ≠ g.eval z

noncomputable def indicator (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0

/-- The published per-gate estimate. The paper's square-root estimate (`lem:live`) and its weight selection are proved from
it, not assumed. -/
noncomputable def CTW26_AppendixA3_CentralBinomialRestriction : Prop := by
  classical
  exact ∀ (n k : ℕ), 0 < k → k < n → ∀ g : RealThresholdGate n,
    mean (fun ρ : FiniteRestriction n k => indicator (gateLive g ρ)) ≤
      ((k * Nat.choose (n - k) ((n - k) / 2) : ℕ) : ℝ) / (2 : ℝ) ^ (n - k)

/-- Mutual independence under uniform averaging, stated as joint-event
factorization for every finite subfamily (a hypothesis of the inequality).
For each i the range of Y i is finite. Any real event can be replaced by its
intersection with that finite range, a Borel set with the same preimage, so
this imposes no stronger notion of independence through measurability. -/
noncomputable def finiteIndependent {Samples Terms : Type*} [Fintype Samples]
    (Y : Terms → Samples → ℝ) : Prop := by
  classical
  exact ∀ (S : Finset Terms) (events : Terms → Set ℝ),
    mean (fun sample => indicator (∀ i ∈ S, Y i sample ∈ events i)) =
      ∏ i ∈ S, mean (fun sample => indicator (Y i sample ∈ events i))

/-- The finite uniform K = 1 specialization of the published bounded-variable
Bernstein inequality. The variance is the literal sum of second moments. -/
noncomputable def Vershynin18_Theorem2_8_4_FiniteBernstein : Prop := by
  classical
  exact ∀ (Samples Terms : Type*) [Fintype Samples] [Nonempty Samples]
      [Fintype Terms] [Nonempty Terms] (Y : Terms → Samples → ℝ),
    finiteIndependent Y →
    (∀ i, mean (Y i) = 0) →
    (∀ i sample, |Y i sample| ≤ 1) →
    ∀ s : ℝ, 0 < s →
      mean (fun sample => indicator (s ≤ |∑ i, Y i sample|)) ≤
        2 * Real.exp (-(s ^ 2) /
          (2 * ((∑ i, mean (fun sample => (Y i sample) ^ 2)) + s / 3)))

end NearCubicGates.PublishedSources.Witness

end

/-! ## 24. Input 9: the three-query PCPP and the linear code (CW19 Lemmas 24 and 27) -/

section

set_option autoImplicit false
namespace NearCubicGates.PublishedSources.PCPP
open NearCubicWires
open NearCubicWires.SourceInterfaces
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource
open NearCubicWires.Bindings.CLW20Lemma311

structure LinearCodeFamily where
  length : ℕ → ℕ
  support : (n : ℕ) → Fin (length n) → Finset (Fin n)
  decoder : (n : ℕ) → BitInput (length n) → BitInput n

noncomputable def LinearCodeFamily.enc (E : LinearCodeFamily)
    (n : ℕ) (x : BitInput n) : BitInput (E.length n) :=
  fun i => parityOn (E.support n i) x

abbrev MessageRequest := Σ n : ℕ, {_x : BitInput n // 2 ≤ n}

def messageWord (p : MessageRequest) : List Bool :=
  RepairOrdinary.frame p.1.bits ++ RepairOrdinary.frame (List.ofFn p.2.val)

abbrev CodewordRequest (E : LinearCodeFamily) :=
  Σ n : ℕ, {_y : BitInput (E.length n) // 2 ≤ n}

def codewordWord (E : LinearCodeFamily) (p : CodewordRequest E) : List Bool :=
  RepairOrdinary.frame p.1.bits ++ RepairOrdinary.frame (List.ofFn p.2.val)

/-- CW19 Lemma 27's constant-rate linear code, in explicit support form.
The n/2 support claim is stated for n ≥ 2. -/
def EfficientLinearCodeLiteral : Prop :=
  ∃ E : LinearCodeFamily, ∃ distance radius : ℝ,
    0 < radius ∧ radius < distance ∧ distance < 1 ∧
    (∃ K : ℕ, ∀ n, 2 ≤ n → E.length n ≤ K * (n + 1)) ∧
    (∀ n, 2 ≤ n → ∀ i, (E.support n i).card ≤ n / 2) ∧
    (∀ n, 2 ≤ n → ∀ x y : BitInput n, x ≠ y →
      distance ≤ relativeHamming (E.enc n x) (E.enc n y)) ∧
    (∀ n, 2 ≤ n → ∀ x : BitInput n, ∀ y : BitInput (E.length n),
      relativeHamming (E.enc n x) y ≤ radius → E.decoder n y = x) ∧
    Nonempty (Turing.TM2ComputableInPolyTime messageWord
      (fun word : List Bool => word) (fun p => List.ofFn (E.enc p.1 p.2.val))) ∧
    Nonempty (Turing.TM2ComputableInPolyTime (codewordWord E)
      (fun word : List Bool => word) (fun p => List.ofFn (E.decoder p.1 p.2.val)))

/-- The encoder half of `EfficientLinearCodeLiteral`, which is all the main proof uses: a constant-rate linear
code family of positive relative distance whose encoder is a polynomial-time TM2 machine. The systematic
parity-check reduction (`(x, Enc x)`: check the second block against the encoding of the first, and `D` on the
first) needs no decoder, decoding radius or support bound. `EfficientLinearCodeLiteral` implies it by projection. -/
def EfficientLinearEncoder : Prop :=
  ∃ E : LinearCodeFamily, ∃ distance : ℝ,
    0 < distance ∧ distance < 1 ∧
    (∃ K : ℕ, ∀ n, 2 ≤ n → E.length n ≤ K * (n + 1)) ∧
    (∀ n, 2 ≤ n → ∀ x y : BitInput n, x ≠ y →
      distance ≤ relativeHamming (E.enc n x) (E.enc n y)) ∧
    Nonempty (Turing.TM2ComputableInPolyTime messageWord
      (fun word : List Bool => word)
      (fun p => List.ofFn (E.enc p.1 p.2.val)))

structure RawThreeQueryPCPP (n : ℕ) where
  proofBits : ℕ
  randomBits : ℕ
  clause : Fin (2 ^ randomBits) → Fin 3 → Literal (n + proofBits)

def RawThreeQueryPCPP.accepts {n : ℕ} (P : RawThreeQueryPCPP n)
    (input : BitInput n) (proof : BitInput P.proofBits)
    (coins : Fin (2 ^ P.randomBits)) : Bool :=
  (List.ofFn fun i : Fin 3 => (P.clause coins i).eval (Fin.addCases input proof)).any id

noncomputable def RawThreeQueryPCPP.fraction {n : ℕ} (P : RawThreeQueryPCPP n)
    (input : BitInput n) (proof : BitInput P.proofBits) : ℝ :=
  ((Finset.univ.filter fun coins => P.accepts input proof coins = true).card : ℝ) /
    (2 ^ P.randomBits : ℝ)

def RawThreeQueryPCPP.word {n : ℕ} (P : RawThreeQueryPCPP n) : List Bool :=
  RepairOrdinary.frame P.proofBits.bits ++ RepairOrdinary.frame P.randomBits.bits ++
    (List.ofFn fun coins : Fin (2 ^ P.randomBits) =>
      (List.ofFn fun i : Fin 3 =>
        RepairOrdinary.frame (literalCode (P.clause coins i)).bits).flatten).flatten

def ProximityFar (delta : ℝ) (C : Circuit) (input : BitInput C.n) : Prop :=
  ∀ accepted : BitInput C.n, C.D.eval accepted = true →
    delta ≤ relativeHamming input accepted

abbrev AcceptedCircuitInput := Σ C : Circuit, {x : BitInput C.n // C.D.eval x = true}

def acceptedCircuitInputWord (p : AcceptedCircuitInput) : List Bool :=
  p.1.word ++ List.ofFn p.2.val

/-- CW19 Lemma 24: three queries, OR predicates, proximity soundness,
perfect completeness, and a uniform honest-proof procedure on YES inputs. -/
def PerfectThreeQueryProximityLiteral : Prop :=
  ∀ delta : ℝ, 0 < delta → delta < 1 →
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧
    ∃ output : (C : Circuit) → RawThreeQueryPCPP C.n,
      Nonempty (Turing.TM2ComputableInPolyTime (fun C : Circuit => C.word)
        (fun word : List Bool => word) (fun C => (output C).word)) ∧
      (∃ K e : ℕ, ∀ C,
        (output C).proofBits ≤ K * (C.m + 1) ^ e ∧
        2 ^ (output C).randomBits ≤ K * (C.m + 1) ^ e) ∧
      (∀ C input, ProximityFar delta C input →
        ∀ proof, (output C).fraction input proof ≤ s) ∧
      ∃ honest : (p : AcceptedCircuitInput) → BitInput (output p.1).proofBits,
        (∀ p coins, (output p.1).accepts p.2.val (honest p) coins = true) ∧
        Nonempty (Turing.TM2ComputableInPolyTime acceptedCircuitInputWord
          (fun word : List Bool => word) (fun p => List.ofFn (honest p)))

/-- Input 9: the three-query proximity verifier (CW19 Lemma 24) and an efficient linear encoder (the encoder of
CW19 Lemma 27's code). The pointwise form the paper uses (`imp:three-pcpp`) is proved from them. -/
def ThreeQuerySourceGroup : Prop :=
  PerfectThreeQueryProximityLiteral ∧ EfficientLinearEncoder

end NearCubicGates.PublishedSources.PCPP

end

/-! ## 25. Input 6: the short PCP as an oracle circuit (Murray–Williams 2020) -/

section

section
namespace NearCubicWires.Bindings.MW20
open NearCubicWires NearCubicWires.CanonicalBinary NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.LocalBitMultitape
set_option autoImplicit false

/-- One node of an oracle circuit on `n` inputs whose oracle gates have `arity` inputs: the nodes of
`BooleanCircuit` (constants, inputs, fan-in-two AND and OR, NOT) and one oracle gate, whose `arity` argument
wires are earlier nodes. -/
inductive OracleNode (n arity : ℕ) where
  | const (value : Bool)
  | input (index : Fin n)
  | not (child : ℕ)
  | and (left right : ℕ)
  | or (left right : ℕ)
  | oracle (args : Fin arity → ℕ)

/-- Every child of the node at position `index` precedes it. -/
def OracleNode.WellFormedAt {n arity : ℕ} (index : ℕ) : OracleNode n arity → Prop
  | .const _ => True
  | .input _ => True
  | .not child => child < index
  | .and left right => left < index ∧ right < index
  | .or left right => left < index ∧ right < index
  | .oracle args => ∀ j, args j < index

/-- The value of a node, given the values `prior` of the earlier nodes; an oracle gate returns
`O` applied to the values of its argument wires. -/
def OracleNode.eval {n arity : ℕ} (O : BitInput arity → Bool) (input : BitInput n)
    (prior : Array Bool) : OracleNode n arity → Bool
  | .const value => value
  | .input index => input index
  | .not child => !(prior[child]?.getD false)
  | .and left right => prior[left]?.getD false && prior[right]?.getD false
  | .or left right => prior[left]?.getD false || prior[right]?.getD false
  | .oracle args => O fun j => prior[args j]?.getD false

/-- "an oracle circuit C^O": a topologically ordered DAG of `OracleNode`s with a designated output node,
exactly like `BooleanCircuit`, plus oracle gates of arity `arity`. -/
structure OracleCircuit (n arity : ℕ) where
  nodes : List (OracleNode n arity)
  output : Fin nodes.length
  wellFormed : ∀ index : Fin nodes.length, (nodes.get index).WellFormedAt index.val

/-- The values of all nodes of `C^O` on `input`. -/
def OracleCircuit.values {n arity : ℕ} (C : OracleCircuit n arity) (O : BitInput arity → Bool)
    (input : BitInput n) : Array Bool :=
  C.nodes.foldl (fun prior node => prior.push (node.eval O input prior)) #[]

/-- `C^O(input)`. -/
def OracleCircuit.eval {n arity : ℕ} (C : OracleCircuit n arity) (O : BitInput arity → Bool)
    (input : BitInput n) : Bool :=
  (C.values O input)[C.output.val]?.getD false

/-- The size: the number of nodes (input, constant and oracle nodes included), as `BooleanCircuit.size`. -/
def OracleCircuit.size {n arity : ℕ} (C : OracleCircuit n arity) : ℕ :=
  C.nodes.length

/-- The word of a node, in the native three-field form of the Boolean nodes (tag, then two numbers, `0` when unused:
`0` constant, `1` input, `2` NOT, `3` AND, `4` OR); an oracle gate is tag `5` followed by its `arity` argument wires.
Every field is a self-delimiting `natWord`. -/
def oracleNodeWord {n arity : ℕ} : OracleNode n arity → List Bool
  | .const value => natWord 0 ++ natWord value.toNat ++ natWord 0
  | .input index => natWord 1 ++ natWord index.val ++ natWord 0
  | .not child => natWord 2 ++ natWord child ++ natWord 0
  | .and left right => natWord 3 ++ natWord left ++ natWord right
  | .or left right => natWord 4 ++ natWord left ++ natWord right
  | .oracle args => natWord 5 ++ (List.ofFn fun j => natWord (args j)).flatten

/-- "an oracle circuit C^O_x" with "ℓ inputs", "each copy of the oracle gate O in C^O_x has ℓ inputs as
well": the number `ℓ` and the circuit. -/
structure OracleOutput where
  ell : ℕ
  circuit : OracleCircuit ell ell

/-- The output word: `ℓ` (the number of inputs and the oracle arity), the number of nodes, the node words in order,
then the output address. -/
def OracleOutput.word (o : OracleOutput) : List Bool :=
  natWord o.ell ++ natWord o.circuit.nodes.length ++ o.circuit.nodes.flatMap oracleNodeWord ++
    natWord o.circuit.output.val

/-- The number of satisfying assignments of `C^O`. -/
def OracleOutput.satCount (o : OracleOutput) (O : BitInput o.ell → Bool) : ℕ :=
  (Finset.univ.filter fun z : BitInput o.ell => o.circuit.eval O z = true).card

/-- "every verifier algorithm V(x, y) running in time T(n)": on EVERY `(x, y)` with `|x| = n`, `V` halts within `T(n)`
steps. -/
def RunsInTime (V : OrdinaryVerifier) (T : ℕ → ℕ) : Prop :=
  ∀ n (x : BitInput n) (y : List Bool), ∃ receipt,
    run V.machine (T n) (V.inputTapes (List.ofFn x) y) = some receipt

/-- **Input 6: the short PCP as an oracle circuit (Murray–Williams 2020, Section 5, in the proof of Theorem 1.4,
pp. STOC18-316–STOC18-317, PDF pp. 18–19)**, verbatim:
"for every verifier algorithm V(x, y) running in time T(n) ≥ n, they give an algorithm A running in
poly(n, log T(n)) time which, given x ∈ {0,1}^n, outputs an oracle circuit C^O_x with the following
properties:
• C^O_x has ℓ = log2(T(n)) + O(log log T(n)) inputs, poly(n, log T(n)) size, and each copy of the oracle
  gate O in C^O_x has ℓ inputs as well.
• If there is a y of length T(n) such that V(x, y) accepts, then there is an oracle O : {0,1}^ℓ → {0,1}
  such that C^O_x is unsatisfiable.
• If V(x, y) rejects on all y of length T(n), then for every oracle O : {0,1}^ℓ → {0,1}, C^O_x has at
  least 2^ℓ · (1 − 1/n) satisfying assignments."
Readings: the hidden constants are chosen after `V` and `T`; `T` is not assumed time-constructible, so `A`
receives `T(n)` in binary with `x`; `A` is a Mathlib polynomial-time TM2 machine (`Turing.TM2ComputableInPolyTime`);
the properties are claimed for `n ≥ 1` ("1/n"); `ℓ = log₂T + O(log log T)` is read as its upper half
`2^ℓ ≤ K·T·L(T)^e` with `L = logScale`. -/
def MW20_OracleCircuitPCP_TM2 : Prop :=
  ∀ (V : OrdinaryVerifier) (T : ℕ → ℕ), (∀ n, n ≤ T n) → RunsInTime V T →
  ∃ out : InputRequest → OracleOutput,
    -- "an algorithm A running in poly(n, log T(n)) time which, given x ∈ {0,1}^n, outputs an oracle
    -- circuit C^O_x"
    Nonempty (Turing.TM2ComputableInPolyTime
      (fun x : InputRequest => frame (List.ofFn x.2) ++ frame (T x.1).bits)
      (fun w : List Bool => w) (fun x => (out x).word)) ∧
    -- "ℓ = log2(T(n)) + O(log log T(n)) inputs"
    (∃ K e : ℕ, ∀ x : InputRequest, 1 ≤ x.1 →
      2 ^ (out x).ell ≤ K * T x.1 * logScale (T x.1) ^ e) ∧
    -- "poly(n, log T(n)) size"
    (∃ K e : ℕ, ∀ x : InputRequest, 1 ≤ x.1 →
      (out x).circuit.size ≤ K * (x.1 + natBitLength (T x.1) + 1) ^ e) ∧
    -- "If there is a y of length T(n) such that V(x, y) accepts, then there is an oracle
    -- O : {0,1}^ℓ → {0,1} such that C^O_x is unsatisfiable."
    (∀ x : InputRequest, 1 ≤ x.1 →
      (∃ y : BitInput (T x.1), V.accepts (List.ofFn x.2) (List.ofFn y)) →
      ∃ O : BitInput (out x).ell → Bool, ∀ z, (out x).circuit.eval O z = false) ∧
    -- "If V(x, y) rejects on all y of length T(n), then for every oracle O : {0,1}^ℓ → {0,1}, C^O_x has
    -- at least 2^ℓ · (1 − 1/n) satisfying assignments."
    (∀ x : InputRequest, 1 ≤ x.1 →
      (¬ ∃ y : BitInput (T x.1), V.accepts (List.ofFn x.2) (List.ofFn y)) →
      ∀ O : BitInput (out x).ell → Bool,
        (2 : ℝ) ^ (out x).ell * (1 - 1 / (x.1 : ℝ)) ≤ ((out x).satCount O : ℝ))

/-- A polynomial-time ordinary word function from `input` to `output`: an ordinary program that, started on
`frame (input a)`, writes `output a` within `K · (|input a| + 1)^e` steps. -/
def OrdinaryPolyTime {A : Type} (input output : A → List Bool) : Prop :=
  ∃ K e : ℕ, Nonempty (NearCubicWires.RepairOrdinary.WordFunction A input output
    (fun a => K * ((input a).length + 1) ^ e))

/-- **Input 6 in the ordinary machine model**: `MW20_OracleCircuitPCP_TM2` with the algorithm `A` an ordinary
polynomial-time word function (`OrdinaryPolyTime`) instead of a Mathlib TM2 machine. The quantifier order (for
every `V` and `T`, an output map), the clock `T(n)` given in binary with `x`, and the four printed properties are
those of `MW20_OracleCircuitPCP_TM2`; the polynomial-overhead simulation into TM2 turns this form into that one. -/
def OrdinaryOracleCircuitPCP : Prop :=
  ∀ (V : OrdinaryVerifier) (T : ℕ → ℕ), (∀ n, n ≤ T n) → RunsInTime V T →
  ∃ out : InputRequest → OracleOutput,
    -- "an algorithm A running in poly(n, log T(n)) time which, given x ∈ {0,1}^n, outputs an oracle
    -- circuit C^O_x"
    OrdinaryPolyTime
      (fun x : InputRequest => frame (List.ofFn x.2) ++ frame (T x.1).bits)
      (fun x => (out x).word) ∧
    -- "ℓ = log2(T(n)) + O(log log T(n)) inputs"
    (∃ K e : ℕ, ∀ x : InputRequest, 1 ≤ x.1 →
      2 ^ (out x).ell ≤ K * T x.1 * logScale (T x.1) ^ e) ∧
    -- "poly(n, log T(n)) size"
    (∃ K e : ℕ, ∀ x : InputRequest, 1 ≤ x.1 →
      (out x).circuit.size ≤ K * (x.1 + natBitLength (T x.1) + 1) ^ e) ∧
    -- "If there is a y of length T(n) such that V(x, y) accepts, then there is an oracle
    -- O : {0,1}^ℓ → {0,1} such that C^O_x is unsatisfiable."
    (∀ x : InputRequest, 1 ≤ x.1 →
      (∃ y : BitInput (T x.1), V.accepts (List.ofFn x.2) (List.ofFn y)) →
      ∃ O : BitInput (out x).ell → Bool, ∀ z, (out x).circuit.eval O z = false) ∧
    -- "If V(x, y) rejects on all y of length T(n), then for every oracle O : {0,1}^ℓ → {0,1}, C^O_x has
    -- at least 2^ℓ · (1 − 1/n) satisfying assignments."
    (∀ x : InputRequest, 1 ≤ x.1 →
      (¬ ∃ y : BitInput (T x.1), V.accepts (List.ofFn x.2) (List.ofFn y)) →
      ∀ O : BitInput (out x).ell → Bool,
        (2 : ℝ) ^ (out x).ell * (1 - 1 / (x.1 : ℝ)) ≤ ((out x).satCount O : ℝ))

end NearCubicWires.Bindings.MW20
end

end

/-! ## 26. Input 8 and the nine inputs: `NineInputs`, `NineFinalStatement` -/

section

set_option autoImplicit false
namespace NearCubicGates.Close

/-- Input 8: CLW20 Lemma 3.9 with "time-constructible" in the standard multitape sense, the same
`TimeConstructible` as input 7 (`CLW20Theorem113.TimeConstructible`: a multitape machine computes the binary `S(n)`
from unary `n` within `C·(S(n)+1)` steps); the amplifier itself is `Lemma3_9AtTM2`. CLW20, PDF p. 18: "There is a
constant c ≥ 1 such that, for any time-constructible function S(n) and every f ..." -/
def CLW20_Lemma3_9_Multitape : Prop :=
  ∃ c : ℝ, 1 ≤ c ∧ ∀ S : ℕ → ℕ, NearCubicWires.Bindings.CLW20Theorem113.TimeConstructible S →
    Nonempty (NearCubicWires.Bindings.CLW20Lemma39TM2.Lemma3_9AtTM2 c S)

/-- The nine inputs from which `main_from_inputs` proves the main theorem. -/
structure NineInputs : Prop where
  normalization : NearCubicWires.Bindings.CTW26.CTW26_Lemma3_2
  restriction : NearCubicGates.PublishedSources.Witness.CTW26_AppendixA3_CentralBinomialRestriction
  bernstein : NearCubicGates.PublishedSources.Witness.Vershynin18_Theorem2_8_4_FiniteBernstein.{0, 0}
  primes : NearCubicGates.PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem
  rectangularProduct : NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4
  shortPCP : NearCubicWires.Bindings.MW20.OrdinaryOracleCircuitPCP
  refuter : NearCubicWires.Bindings.CLW20Theorem113.CLW20_Theorem1_13
  amplification : CLW20_Lemma3_9_Multitape
  threeQueryPCPP : NearCubicGates.PublishedSources.PCPP.ThreeQuerySourceGroup

/-- The main theorem from the nine inputs. -/
def NineFinalStatement : Prop := NineInputs → NearCubicGates.Target.MainStatement

end NearCubicGates.Close

end
