import Proof.Foundations.SourceCore
import Proof.Foundations.OrdinaryRewindCarrier
import Proof.Foundations.SupplierPipeline
import Proof.Foundations.OuterPCPRecovery
import Proof.Foundations.OperationalWilliamsSourceCore
import StatementSupport

/-!
# Representation-sensitive literature interfaces

Ordinary source algorithms are retained
with literal finite-machine receipts. Locally strengthened codecs, queries,
ceil-root transport, rational resources and physical closure are separate
obligations, never additional literature fields. No legacy PublishedContracts
or impossible executable-source witness is used here.
-/
namespace NearCubicWires.RepairRepresentation

open SourceInterfaces ExecutableInterfaces RepairSource LocalBitMultitape CanonicalBinary
open SupplierPipeline RecoveryPipeline OuterPCPRecovery CompilerSemantics
open WilliamsPublishedForm
open WilliamsProductCertificate
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## Conventional explicit binary words: linear sequence structure -/

def thresholdWord {n : ℕ} (g : NormalizedThresholdGate n) : List Bool :=
  natWord n ++ (List.ofFn g.weight).flatMap intWord ++ intWord g.threshold

def exactWord {n : ℕ} (g : ExactThresholdGate n) : List Bool :=
  (List.ofFn g.weight).flatMap intWord ++ intWord g.target

def exactListWord {n : ℕ} (gs : List (ExactThresholdGate n)) : List Bool :=
  natWord gs.length ++ gs.flatMap exactWord

/-! ## CW19 qualitative disjoint exact conversion

CW19 Proposition18(2): a polynomial-time explicit construction. The source
does not include AppendixA.12's repaired sharp child/coefficient envelopes.
The word format is ordinary streaming binary, not recursive Encodable lists.
-/

structure DecompositionAlgorithm where
  output : (r : ExactDecompositionRequest) → ExactDecomposition r.gate
  coefficient : ℕ
  degree : ℕ
  coefficientPositive : 0 < coefficient
  constructor : OrdinaryWordFunction ExactDecompositionRequest
    (fun r => thresholdWord r.gate)
    (fun r => exactListWord (output r).children)
    (fun r => coefficient * (r.arity + r.gate.encodingBits + 1) ^ degree)

def DecompositionSource : Prop := Nonempty DecompositionAlgorithm

/-- Exact same normalized retained top used by SupplierPipeline.topDecomposition,
with only the unsupported executable wrapper removed. -/
def retainedTopDecomposition (a : DecompositionAlgorithm) {n : ℕ}
    (c : NormalizedThresholdThresholdCircuit n) :
    ExactDecomposition (nonStrictAsStrict (retainedTopGate c)) :=
  a.output ⟨c.top.support.card, nonStrictAsStrict (retainedTopGate c)⟩

theorem retainedTop_equivalent (a : DecompositionAlgorithm) {n : ℕ}
    (c : NormalizedThresholdThresholdCircuit n) (x : BitInput n) :
    c.eval x = (retainedTopDecomposition a c).children.any
      (fun child => child.eval (retainedBottomValues c x)) := by
  rw [← (retainedTopDecomposition a c).equivalent (retainedBottomValues c x)]
  rw [← retainedTopGate_eval c x]
  exact (nonStrictAsStrict_eval (retainedTopGate c) (retainedBottomValues c x)).symm

/-- The actual disjoint child-count expression, rather than a semantic OR
whose resource count has been silently substituted. -/
theorem retainedTop_count (a : DecompositionAlgorithm) {n : ℕ}
    (c : NormalizedThresholdThresholdCircuit n) (x : BitInput n) :
    ((retainedTopDecomposition a c).children.filter
      (fun child => child.eval (retainedBottomValues c x))).length = (c.eval x).toNat := by
  rw [filterLength_eq_any_toNat _ _
    ((retainedTopDecomposition a c).disjoint (retainedBottomValues c x))]
  rw [← retainedTop_equivalent]

/-- LOCAL codec/count realization, not part of CW's imported theorem. The
ordinary explicit output yields a polynomial count through fresh-tape growth;
the sharper A.12 bound and balanced-word conversion are proved locally. -/
structure DecompositionLocalBounds (a : DecompositionAlgorithm) where
  coefficient : ℕ
  degree : ℕ
  coefficientPositive : 0 < coefficient
  children : ∀ r, (a.output r).children.length ≤
    coefficient * (r.arity + r.gate.encodingBits + 1) ^ degree
  balancedOutput : ExactDecompositionRequest → ℕ
  balancedDecode : ∀ r,
    decodeBalancedList (balancedOutput r) =
      some ((a.output r).children.map (fun child =>
        encodeBalancedList ((List.ofFn child.weight).map encodeInt ++ [encodeInt child.target])))
  balancedBits : ∀ r, natBitLength (balancedOutput r) ≤
    coefficient * (r.arity + r.gate.encodingBits + 1) ^ degree
  balancedSerializer : OrdinaryWordFunction ExactDecompositionRequest
    (fun r => natWord r.arity ++ exactListWord (a.output r).children)
    (fun r => (balancedOutput r).bits)
    (fun r => coefficient * (r.arity + r.gate.encodingBits + 1) ^ degree)

/-! ## WilACC14: exact integer product on framed ordinary tapes

Corollaries4.4/C.2 on exact tenth powers. Ceil-root padding/cropping belongs
to the local caller. Fixed finite small cases and conventional formatting
are absorbed into the coefficient; output is on a fresh tape.
-/

structure ExactPowerRequest where
  inner : ℕ
  positive : 1 ≤ inner
  left : BitMatrix (inner ^ 10) inner
  right : BitMatrix inner (inner ^ 10)

def ExactPowerRequest.dimension (r : ExactPowerRequest) : ℕ := r.inner ^ 10

def ExactPowerRequest.output (r : ExactPowerRequest) : List Bool :=
  WilliamsLoaderForms.encodedNatCellTape
    (natBitLength r.dimension) (rowMajorNatMatrix (integerMatrixProduct r.left r.right))

structure WilliamsAlgorithm where
  tapeCount : ℕ
  stateCount : ℕ
  threeTapes : 3 ≤ tapeCount
  machine : Machine tapeCount stateCount
  outputTape : Fin tapeCount
  outputFreshLeft : outputTape.val ≠ 0
  outputFreshRight : outputTape.val ≠ 1
  coefficient : ℕ
  logExponent : ℕ
  coefficientPositive : 0 < coefficient
  runs : ∀ r : ExactPowerRequest, ∃ receipt,
    run machine (coefficient * r.dimension ^ 2 * logScale r.dimension ^ logExponent)
      (fun tape => if tape.val = 0 then
        natWord r.dimension ++ WilliamsLoaderForms.rowMajorBitMatrix r.left
       else if tape.val = 1 then
        WilliamsLoaderForms.rowMajorBitMatrix r.right
       else []) = some receipt ∧
      receipt.final.tapes outputTape = r.output

def WilliamsSource : Prop := Nonempty WilliamsAlgorithm

/-- A LOCAL ordinary wrapper for actual ceiling-dimension requests. Its
implementation loads both inputs, calls the selected source once, crops and
copies once. This record is an implementation obligation, not an import. -/
structure WilliamsCeilRealization (source : WilliamsAlgorithm) where
  coefficient : ℕ
  logExponent : ℕ
  coefficientPositive : 0 < coefficient
  sourceExponentPaid : source.logExponent ≤ logExponent
  wrapper : OrdinaryWordFunction RectangularProductRequest
    (fun r => natWord r.dimension ++
      WilliamsLoaderForms.rowMajorBitMatrix r.left ++
      WilliamsLoaderForms.rowMajorBitMatrix r.right)
    (fun r => WilliamsLoaderForms.encodedNatCellTape
      (natBitLength r.dimension) (rowMajorNatMatrix (integerMatrixProduct r.left r.right)))
    (fun r => coefficient * (r.dimension + 1) ^ 2 * (logScale r.dimension + 1) ^ logExponent)

/-- Literal surviving residual factor in the S3 column parent. No register
fuel is converted into bit time by this arithmetic application. -/
theorem williams_residual_charge (C e U q residual : ℕ)
    (hU : U ^ 2 ≤ 2 * residual) (hlog : logScale U ≤ q + 2) :
    C * U ^ 2 * logScale U ^ e ≤ 2 * C * residual * (q + 2) ^ e := by
  calc
    _ ≤ C * (2 * residual) * (q + 2) ^ e := by gcongr
    _ = _ := by ring

theorem product_entry_le_inner {rows inner columns : ℕ}
    (left : BitMatrix rows inner) (right : BitMatrix inner columns)
    (row : Fin rows) (column : Fin columns) :
    integerMatrixProduct left right row column ≤ inner := by
  unfold integerMatrixProduct
  calc
    _ ≤ ∑ _i : Fin inner, 1 := by
      apply Finset.sum_le_sum
      intro i _
      split <;> omega
    _ = inner := by simp

theorem exactPower_output_length (r : ExactPowerRequest) :
    r.output.length = r.dimension ^ 2 * natBitLength r.dimension := by
  simp [ExactPowerRequest.output, WilliamsLoaderForms.encodedNatCellTape,
    WilliamsLoaderForms.fixedWidthNatBits, List.length_flatMap,
    rowMajorNatMatrix_length, ExactPowerRequest.dimension, pow_two]

/-- The literal source call, including its actual final output and transition
charge. This consumes a source run; it does not construct a Williams machine. -/
theorem williams_source_call (a : WilliamsAlgorithm) (r : ExactPowerRequest)
    (q residual : ℕ) (hU : r.dimension ^ 2 ≤ 2 * residual)
    (hlog : logScale r.dimension ≤ q + 2) :
    ∃ receipt,
      run a.machine (a.coefficient * r.dimension ^ 2 * logScale r.dimension ^ a.logExponent)
        (fun tape => if tape.val = 0 then
          natWord r.dimension ++ WilliamsLoaderForms.rowMajorBitMatrix r.left
         else if tape.val = 1 then WilliamsLoaderForms.rowMajorBitMatrix r.right
         else []) = some receipt ∧
      receipt.final.tapes a.outputTape = r.output ∧
      receipt.steps ≤ 2 * a.coefficient * residual * (q + 2) ^ a.logExponent := by
  obtain ⟨receipt, hrun, hout⟩ := a.runs r
  refine ⟨receipt, hrun, hout, ?_⟩
  exact (RepairOrdinary.runFrom_steps_le a.machine _ _ receipt hrun).trans
    (williams_residual_charge a.coefficient a.logExponent r.dimension q residual hU hlog)

/-- Exact enclosing charge for the locally realized arbitrary-dimension
wrapper. Its +1 totality convention costs factor8, not another residual. -/
theorem williams_wrapper_budget (a : WilliamsAlgorithm) (localRun : WilliamsCeilRealization a)
    (r : RectangularProductRequest) (q residual : ℕ)
    (hpositive : 1 ≤ r.dimension) (hU : r.dimension ^ 2 ≤ 2 * residual)
    (hlog : logScale r.dimension ≤ q + 2) :
    localRun.coefficient * (r.dimension + 1) ^ 2 *
      (logScale r.dimension + 1) ^ localRun.logExponent ≤
        8 * localRun.coefficient * residual * (q + 3) ^ localRun.logExponent := by
  have hsquare : (r.dimension + 1) ^ 2 ≤ 8 * residual := by nlinarith
  calc
    _ ≤ localRun.coefficient * (8 * residual) * (q + 3) ^ localRun.logExponent := by
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hsquare)
        (Nat.pow_le_pow_left (by omega : logScale r.dimension + 1 ≤ q + 3) _)
    _ = _ := by ring

/-- Actual parent application after the named local pad/crop/source wrapper
is supplied, with the SAME receipt's output and ordinary step bound. -/
theorem williams_column_call (a : WilliamsAlgorithm) (localRun : WilliamsCeilRealization a)
    (r : RectangularProductRequest) (q residual : ℕ)
    (hpositive : 1 ≤ r.dimension) (hU : r.dimension ^ 2 ≤ 2 * residual)
    (hlog : logScale r.dimension ≤ q + 2) :
    ∃ receipt,
      run localRun.wrapper.program.machine
        (localRun.coefficient * (r.dimension + 1) ^ 2 *
          (logScale r.dimension + 1) ^ localRun.logExponent)
        (localRun.wrapper.program.inputTapes
          (natWord r.dimension ++ WilliamsLoaderForms.rowMajorBitMatrix r.left ++
            WilliamsLoaderForms.rowMajorBitMatrix r.right)) = some receipt ∧
      receipt.final.tapes localRun.wrapper.program.outputTape =
        WilliamsLoaderForms.encodedNatCellTape (natBitLength r.dimension)
          (rowMajorNatMatrix (integerMatrixProduct r.left r.right)) ∧
      receipt.steps ≤ 8 * localRun.coefficient * residual * (q + 3) ^ localRun.logExponent := by
  obtain ⟨receipt, hrun, hout⟩ := localRun.wrapper.realizes r
  refine ⟨receipt, hrun, hout, ?_⟩
  exact (RepairOrdinary.runFrom_steps_le localRun.wrapper.program.machine _ _ receipt hrun).trans
    (williams_wrapper_budget a localRun r q residual hpositive hU hlog)

/-! ## CLW20 Lemma3.11: typed pointwise PCPP

The small-arity qualification is necessary for half-support parity. The local
outer-width padding establishes this domain; no guarantee is projected back
to arity one. Both machines are fixed before seeing any circuit or input.
-/

structure PCPPRequest (minimumArity : ℕ) where
  arity : ℕ
  circuit : BooleanCircuit arity
  large : minimumArity ≤ arity
  sizeLarge : arity ≤ circuit.size

def pcppInput {n0 : ℕ} (r : PCPPRequest n0) : List Bool :=
  natWord r.arity ++ (encodeBooleanCircuit r.circuit).bits

def pcppOutput {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit) : List Bool :=
  natListWord [p.systematicBits, p.auxiliaryBits, p.clauseBits] ++
    (List.ofFn (fun i : Fin p.systematicBits =>
      List.ofFn (fun j : Fin r.arity => decide (j ∈ p.systematicSupport i)))).flatten ++
    natListWord ((List.ofFn fun i : Fin (2 ^ p.clauseBits) =>
      [literalIndex (p.clauses i).left, literalIndex (p.clauses i).right]).flatten)

structure PointwisePCPPAlgorithm where
  minimumArity : ℕ
  minimumArityBound : 2 ≤ minimumArity
  completeness : ℝ
  soundness : ℝ
  soundnessPositive : 0 < soundness
  gap : soundness < completeness
  completenessBelowOne : completeness < 1
  coefficient : ℕ
  degree : ℕ
  coefficientPositive : 0 < coefficient
  output : (r : PCPPRequest minimumArity) → PointwisePCPP r.circuit
  systematicBound : ∀ r, (output r).systematicBits ≤ coefficient * (r.arity + 1) ^ degree
  auxiliaryBound : ∀ r, (output r).auxiliaryBits ≤ coefficient * (r.circuit.size + 1) ^ degree
  clauseCountBound : ∀ r, 2 ^ (output r).clauseBits ≤ coefficient * (r.circuit.size + 1) ^ degree
  constructor : OrdinaryWordFunction (PCPPRequest minimumArity) pcppInput
    (fun r => pcppOutput r (output r))
    (fun r => coefficient * (r.circuit.size + r.arity + 1) ^ degree)
  honest : OrdinaryWordFunction (Σ r : PCPPRequest minimumArity, BitInput r.arity)
    (fun r => pcppInput r.1 ++ List.ofFn r.2)
    (fun r => List.ofFn ((output r.1).honestAuxiliary r.2))
    (fun r => coefficient * (r.1.circuit.size + r.1.arity + 1) ^ degree)
  complete : ∀ r x, r.circuit.eval x = true →
    (output r).satisfiedFraction x ((output r).honestAuxiliary x) ≥ completeness
  sound : ∀ r x, r.circuit.eval x = false → ∀ auxiliary,
    (output r).satisfiedFraction x auxiliary ≤ soundness

def PointwisePCPPSource : Prop := Nonempty PointwisePCPPAlgorithm

def pointwiseRequest (a : PointwisePCPPAlgorithm) {n : ℕ}
    (c : BooleanCircuit n) (hn : a.minimumArity ≤ n) : PCPPRequest a.minimumArity where
  arity := n
  circuit := c.padToArity
  large := hn
  sizeLarge := BooleanCircuit.arity_le_padToArity_size c

/-- The actual size-padded substituted-circuit consumer needs just its typed
circuit and normalized native-width lower bound, not a legacy hierarchy cast. -/
theorem pointwise_padded_complete (a : PointwisePCPPAlgorithm) {n : ℕ}
    (c : BooleanCircuit n) (hn : a.minimumArity ≤ n) (x : BitInput n)
    (hx : c.eval x = true) :
    (a.output (pointwiseRequest a c hn)).satisfiedFraction x
      ((a.output (pointwiseRequest a c hn)).honestAuxiliary x) ≥ a.completeness := by
  apply a.complete
  simpa only [pointwiseRequest, BooleanCircuit.padToArity_eval] using hx

theorem pointwise_padded_sound (a : PointwisePCPPAlgorithm) {n : ℕ}
    (c : BooleanCircuit n) (hn : a.minimumArity ≤ n) (x : BitInput n)
    (hx : c.eval x = false) (auxiliary : BitInput (a.output (pointwiseRequest a c hn)).auxiliaryBits) :
    (a.output (pointwiseRequest a c hn)).satisfiedFraction x auxiliary ≤ a.soundness := by
  apply a.sound
  simpa only [pointwiseRequest, BooleanCircuit.padToArity_eval] using hx

/-- The full enclosing m+n charge after the real oracle-size substitution. -/
theorem pointwise_substitution_budget (a : PointwisePCPPAlgorithm)
    (n m oracleBound Csub dsub : ℕ)
    (hm : m ≤ Csub * (n + oracleBound + 1) ^ dsub + n) :
    a.coefficient * (m + n + 1) ^ a.degree ≤
      a.coefficient * (Csub * (n + oracleBound + 1) ^ dsub + 2 * n + 1) ^ a.degree := by
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  omega

/-- LOCAL full-object reconstruction/lookup adapters. Their requests use
actual finite output ranges. No unchecked raw code or index is admitted. -/
structure PCPPQueryRealization (a : PointwisePCPPAlgorithm) where
  coefficient : ℕ
  degree : ℕ
  coefficientPositive : 0 < coefficient
  support : OrdinaryWordFunction
    (Σ r : PCPPRequest a.minimumArity, Fin (a.output r).systematicBits)
    (fun r => pcppInput r.1 ++ natWord r.2.val)
    (fun r => List.ofFn fun j : Fin r.1.arity => decide (j ∈ (a.output r.1).systematicSupport r.2))
    (fun r => coefficient * (r.1.circuit.size + r.1.arity + 1) ^ degree)
  clause : OrdinaryWordFunction
    (Σ r : PCPPRequest a.minimumArity, Fin (2 ^ (a.output r).clauseBits))
    (fun r => pcppInput r.1 ++ natWord r.2.val)
    (fun r => natListWord [literalIndex ((a.output r.1).clauses r.2).left,
      literalIndex ((a.output r.1).clauses r.2).right])
    (fun r => coefficient * (r.1.circuit.size + r.1.arity + 1) ^ degree)

/-! ## CLW20 Lemma3.8 and its AppendixA sample/affine construction

Full literal projections and output negation are the source's typical-class
operations (PDF15/printed14). AppendixA (PDF50--52) supplies the sampled affine
form below. The rational term/mass/bit envelope and physical-wire closure are
LOCAL consequences, not strengthened fields of the literature theorem.
-/

def LiteralProjectionClosed (family : SizedFunctionFamily) : Prop :=
  ∀ {n m size : ℕ} (f : BoolFunction n), family n f size →
    ∀ p : Fin n → ProjectedRandomBit m,
      family m (fun x => f (fun i => (p i).eval x)) size

def epsilonQ (delta : ℚ) (k : ℕ) : ℚ :=
  (1 - delta) ^ (k - 1) * (1 / 2 - delta)

def alphaQ (delta : ℚ) (j : ℕ) : ℚ :=
  (1 - delta) / ((2 + delta) * epsilonQ delta j)

noncomputable def sampleCount (delta : ℚ) (n j : ℕ) : ℕ :=
  ⌈4 * (n + 1 : ℕ) / ((delta : ℝ) ^ 2 * xorEpsilon (delta : ℝ) j ^ 2)⌉₊

inductive SampleForm (delta : ℚ) (n k : ℕ) : List (ℚ × BoolFunction n) → Prop
  | direct (f : BoolFunction n) : SampleForm delta n k [(1, f)]
  | affine (j : ℕ) (hj : 2 ≤ j) (hjk : j ≤ k)
      (atoms : List (BoolFunction n)) (hcount : atoms.length = sampleCount delta n j)
      (one : BoolFunction n) (hone : ∀ x, one x = true) :
      SampleForm delta n k
        (atoms.map (fun f => (alphaQ delta j / atoms.length, f)) ++
          [((1 - alphaQ delta j) / 2, one)])

structure SampledXorSum (family : SizedFunctionFamily) (delta : ℚ)
    (n k size : ℕ) (f : BoolFunction n) where
  sum : UnitIntervalCircuitSum family n size
  form : SampleForm delta n k sum.terms
  close : l1DistanceFromBoolean f sum.value ≤ (delta : ℝ)

def XorSource : Prop :=
  ∀ (delta : ℚ), 0 < delta → delta < 1 / 2 →
  ∀ (family : SizedFunctionFamily), LiteralProjectionClosed family →
    NegationClosedFamily family →
  ∀ {n : ℕ} (f : BoolFunction n), 1 ≤ n →
  ∀ k size, 1 ≤ k → ∀ candidate : BoolFunction (k * n),
    family (k * n) candidate size →
    1 / 2 + xorEpsilon (delta : ℝ) k < agreement candidate (xorPower f k) →
    Nonempty (SampledXorSum family delta n k size f)

noncomputable def xorTermBound (delta : ℚ) (n k : ℕ) : ℕ :=
  ⌈16 * n / ((delta : ℝ) ^ 2 * xorEpsilon (delta : ℝ) k ^ 2)⌉₊

def xorBits (delta : ℚ) (n k : ℕ) : ℕ :=
  (8 + 5 * natBitLength delta.den) * (n + k + 1)

/-- LOCAL arithmetic representation lemma for the exact sampled coefficients.
It neither selects a new XOR source nor strengthens the imported predicate. -/
def RationalXorResources : Prop :=
  ∀ (delta : ℚ), 0 < delta → delta < 1 / 2 →
  ∀ (family : SizedFunctionFamily) {n k size : ℕ} (f : BoolFunction n),
    1 ≤ n → 1 ≤ k → ∀ w : SampledXorSum family delta n k size f,
      w.sum.terms.length ≤ xorTermBound delta n k ∧
      w.sum.coefficientsWithinBitBound (xorBits delta n k) ∧
      w.sum.coefficientMass ≤ 1 / xorEpsilon (delta : ℝ) k

/-- Literal `FarFromCircuitSums` consumer with the copy-dependent
precision and source closure. The local arithmetic stays explicit. -/
theorem xor_consumer (source : XorSource) (resources : RationalXorResources)
    (delta : ℚ) (hd : 0 < delta) (hhalf : delta < 1 / 2)
    (family : SizedFunctionFamily) (hprojection : LiteralProjectionClosed family)
    (hnegation : NegationClosedFamily family) {n : ℕ} (f : BoolFunction n)
    (hn : 1 ≤ n) (k size : ℕ) (hk : 1 ≤ k)
    (hfar : FarFromCircuitSums family f size (xorTermBound delta n k)
      (xorBits delta n k) (1 / xorEpsilon (delta : ℝ) k) (delta : ℝ))
    (candidate : BoolFunction (k * n)) (hcandidate : family (k * n) candidate size) :
    agreement candidate (xorPower f k) ≤ 1 / 2 + xorEpsilon (delta : ℝ) k := by
  by_contra h
  obtain ⟨w⟩ := source delta hd hhalf family hprojection hnegation f hn k size hk
    candidate hcandidate (lt_of_not_ge h)
  obtain ⟨hterms, hbits, hmass⟩ := resources delta hd hhalf family f hn hk w
  exact (not_lt_of_ge w.close) (hfar w.sum hterms hbits hmass)

theorem xor_fixed_copy_bits (delta : ℚ) (n k : ℕ) :
    xorBits delta n k ≤ (8 + 5 * natBitLength delta.den) * (k + 1) * (n + 1) := by
  unfold xorBits
  have h : n + k + 1 ≤ (k + 1) * (n + 1) := by nlinarith
  exact (Nat.mul_le_mul_left _ h).trans_eq (Nat.mul_assoc ..).symm

end NearCubicWires.RepairRepresentation
