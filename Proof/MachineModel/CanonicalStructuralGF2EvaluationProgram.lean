import Proof.MachineModel.CanonicalBalancedLookupProgram
import Proof.MachineModel.CanonicalBalancedNatSumProgram
import Proof.MachineModel.CanonicalBalancedTraversalParityProgram
import Proof.Circuits.CanonicalForkCall
import Proof.MachineModel.CanonicalFourfoldRowProgram
import Proof.MachineModel.CanonicalNativeCallProgram
import Proof.MachineModel.CanonicalTaggedParityProgram
import Proof.MachineModel.TaggedProgramChoice

/-!
# Executing structural `𝔽₂` polynomials on the oracle machine

`CanonicalFourfoldRowProgram` fixes the structural polynomial representation
used by every canonical row: a `List (List ℕ)` whose inner lists are monomials
of shared residual-variable codes, and whose evaluation
`evaluateStructuralGF2` is the parity of the number of satisfied monomials.
Nothing in the repository executed that evaluation; the row evaluator needs it.

This module supplies the missing machine.  Only two facts about the
representation are used:

* a monomial is satisfied exactly when no variable in it is false, so the
  conjunction is the zero test of one balanced natural sum;
* a polynomial's value is the parity of its monomial bits, which is precisely
  the fixed balanced parity fold already verified for Case 2 seeds.

The assignment stays a link-time program parameter with an exact interpreter
premise and no fuel or callback argument, exactly as the row tail keeps its
`rowEvaluator`.  Register one carries the assignment's context code through
both balanced maps, so no stage rebuilds the table.
-/

namespace NearCubicWires.CanonicalStructuralGF2EvaluationProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLookupProgram
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBalancedTraversalParityProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalForkCall
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalTaggedParityProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedAccuracyDenominatorProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime
open NearCubicWires.SupplierPrinter
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

/-! ## §1 The two arithmetic identities behind the machine -/

/-- A monomial holds exactly when its complemented variable bits sum to zero.
This is the identity that turns the conjunction into one balanced sum. -/
theorem all_eq_decide_sum_eq_zero
    (assignment : ℕ → Bool) (monomial : List ℕ) :
    monomial.all assignment =
      decide
        ((monomial.map fun code => (!assignment code).toNat).sum = 0) := by
  induction monomial with
  | nil => rfl
  | cons code codes inductionHypothesis =>
      simp only [List.all_cons, List.map_cons, List.sum_cons]
      by_cases hcode : assignment code = true
      · simp only [hcode, Bool.true_and, Bool.not_true, Bool.toNat_false,
          Nat.zero_add]
        exact inductionHypothesis
      · have hfalse : assignment code = false := by
          simpa using hcode
        simp [hfalse]

/-- Parity of a Boolean list is the exclusive-or fold.  The machine produces
the fold; `evaluateStructuralGF2` is stated with the parity. -/
theorem foldl_xor_eq_decide_odd
    (values : List Bool) (accumulator : Bool) :
    values.foldl xor accumulator =
      decide
        (Odd (accumulator.toNat + (values.map Bool.toNat).sum)) := by
  induction values generalizing accumulator with
  | nil =>
      cases accumulator <;> simp
  | cons value values inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis (xor accumulator value)]
      simp only [List.map_cons, List.sum_cons]
      refine decide_eq_decide.mpr ?_
      rw [Nat.odd_iff, Nat.odd_iff]
      cases accumulator with
      | false =>
          cases value with
          | false =>
              change (0 + (values.map Bool.toNat).sum) % 2 = 1 ↔
                (0 + (0 + (values.map Bool.toNat).sum)) % 2 = 1
              omega
          | true =>
              change (1 + (values.map Bool.toNat).sum) % 2 = 1 ↔
                (0 + (1 + (values.map Bool.toNat).sum)) % 2 = 1
              omega
      | true =>
          cases value with
          | false =>
              change (1 + (values.map Bool.toNat).sum) % 2 = 1 ↔
                (1 + (0 + (values.map Bool.toNat).sum)) % 2 = 1
              omega
          | true =>
              change (0 + (values.map Bool.toNat).sum) % 2 = 1 ↔
                (1 + (1 + (values.map Bool.toNat).sum)) % 2 = 1
              omega

/-- `evaluateStructuralGF2` in the exact shape the two folds produce. -/
theorem evaluateStructuralGF2_eq_foldl
    (assignment : ℕ → Bool) (polynomial : StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment polynomial =
      (polynomial.map fun monomial => monomial.all assignment).foldl
        xor false := by
  rw [foldl_xor_eq_decide_odd
    (polynomial.map fun monomial => monomial.all assignment) false]
  simp only [Bool.toNat_false, Nat.zero_add, List.map_map]
  rfl

/-! ## §2 The fixed zero test

One four-instruction program serves both Boolean roles the evaluator needs:
complementing a variable bit, and turning the balanced sum of complemented
bits into the monomial's conjunction. -/

def gf2ZeroTestProgram : NPOracleProgram :=
  [ .branchZero 0 1 2
  , .set 0 1 3
  , .set 0 0 3
  , .halt 0
  ]

@[simp] theorem gf2ZeroTestProgram_oracleFree :
    OracleFree gf2ZeroTestProgram := by
  rfl

def gf2ZeroTestFuel : ℕ := 3

private theorem bits_of_boolCode
    {maximumBits : ℕ} (value : Bool) (hpositive : 1 ≤ maximumBits) :
    natBitLength (boolCode value) ≤ maximumBits := by
  have hbits : natBitLength (boolCode value) = 1 := by
    cases value <;> rfl
  rw [hbits]
  exact hpositive

theorem run_gf2ZeroTestProgram
    (inputLength maximumBits code : ℕ) (hpositive : 1 ≤ maximumBits) :
    runNPOracleProgram gf2ZeroTestProgram maximumBits gf2ZeroTestFuel
        (initialNPOracleState inputLength code) =
      some (boolCode (decide (code = 0))) := by
  have hzeroBits : natBitLength (boolCode false) ≤ maximumBits :=
    bits_of_boolCode false hpositive
  have honeBits : natBitLength (boolCode true) ≤ maximumBits :=
    bits_of_boolCode true hpositive
  rw [show gf2ZeroTestFuel = 2 + 1 by rfl]
  rw [run_branchZero_instruction (by rfl) rfl]
  rw [show (initialNPOracleState inputLength code).registers 0 = code by
    simp [initialNPOracleState]]
  by_cases hcode : code = 0
  · rw [if_pos hcode]
    rw [show boolCode (decide (code = 0)) = 1 by simp [hcode, boolCode]]
    rw [show 2 = 1 + 1 by omega]
    rw [run_set_instruction (value := 1) (by rfl) rfl honeBits]
    exact run_halt_instruction (fuel := 0) (value := 1) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) honeBits
  · rw [if_neg hcode]
    rw [show boolCode (decide (code = 0)) = 0 by simp [hcode, boolCode]]
    rw [show 2 = 1 + 1 by omega]
    rw [run_set_instruction (value := 0) (by rfl) rfl hzeroBits]
    exact run_halt_instruction (fuel := 0) (value := 0) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hzeroBits

private theorem decide_boolCode_eq_zero (value : Bool) :
    decide (boolCode value = 0) = !value := by
  cases value <;> rfl

/-! ## §3 One variable of one monomial

The link-time assignment program is the only semantic parameter of the whole
machine.  Its output is complemented here so that a monomial's conjunction
becomes the zero test of a plain natural sum. -/

def gf2VariableProgram (assignmentProgram : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms assignmentProgram gf2ZeroTestProgram

theorem gf2VariableProgram_oracleFree
    (assignmentProgram : NPOracleProgram)
    (hassignment : OracleFree assignmentProgram) :
    OracleFree (gf2VariableProgram assignmentProgram) :=
  oracleFree_linkPrograms hassignment gf2ZeroTestProgram_oracleFree

def gf2VariableFuel (assignmentFuel : ℕ → ℕ) (request : ℕ) : ℕ :=
  linkFuel gf2ZeroTestProgram (assignmentFuel (Nat.unpair request).2)
    gf2ZeroTestFuel

/-- Output of one variable call, as a function of the balanced-call request. -/
def gf2VariableOutput (assignment : ℕ → Bool) (request : ℕ) : ℕ :=
  boolCode (!assignment (Nat.unpair request).2)

theorem run_gf2VariableProgram
    (assignmentProgram : NPOracleProgram) (assignment : ℕ → Bool)
    (assignmentFuel : ℕ → ℕ) (maximumBits contextCode code : ℕ)
    (hpositive : 1 ≤ maximumBits)
    (hcontext : natBitLength contextCode ≤ maximumBits)
    (hassignment :
      runNPOracleProgram assignmentProgram maximumBits (assignmentFuel code)
          (initialNPOracleState contextCode code) =
        some (boolCode (assignment code))) :
    runNPOracleProgram (gf2VariableProgram assignmentProgram) maximumBits
        (gf2VariableFuel assignmentFuel
          (nativeInputRequest contextCode code))
        (initialNPOracleState contextCode code) =
      some
        (gf2VariableOutput assignment
          (nativeInputRequest contextCode code)) := by
  have hcode :
      (Nat.unpair (nativeInputRequest contextCode code)).2 = code := by
    simp [nativeInputRequest]
  rw [gf2VariableFuel, hcode, gf2VariableOutput, hcode]
  rw [show boolCode (!assignment code) =
      boolCode (decide (boolCode (assignment code) = 0)) by
    rw [decide_boolCode_eq_zero]]
  exact run_linkPrograms hpositive hcontext hassignment
    (run_gf2ZeroTestProgram contextCode maximumBits
      (boolCode (assignment code)) hpositive)

def gf2VariableRequests (contextCode : ℕ) (monomial : List ℕ) : List ℕ :=
  monomial.map (nativeInputRequest contextCode)

def gf2VariableOutputs (assignment : ℕ → Bool) (contextCode : ℕ)
    (monomial : List ℕ) : List ℕ :=
  (gf2VariableRequests contextCode monomial).map
    (gf2VariableOutput assignment)

theorem gf2VariableOutputs_eq
    (assignment : ℕ → Bool) (contextCode : ℕ) (monomial : List ℕ) :
    gf2VariableOutputs assignment contextCode monomial =
      monomial.map fun code => (!assignment code).toNat := by
  simp [gf2VariableOutputs, gf2VariableRequests, gf2VariableOutput,
    nativeInputRequest, boolCode]

def gf2MonomialProgram (assignmentProgram : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms
    (linkPrograms nativeInputRequestTreeProgram
      (balancedCallProgram (gf2VariableProgram assignmentProgram)))
    (linkPrograms balancedNatSumProgram gf2ZeroTestProgram)

theorem gf2MonomialProgram_oracleFree
    (assignmentProgram : NPOracleProgram)
    (hassignment : OracleFree assignmentProgram) :
    OracleFree (gf2MonomialProgram assignmentProgram) :=
  oracleFree_linkPrograms
    (oracleFree_linkPrograms nativeInputRequestTreeProgram_oracleFree
      (balancedCallProgram_oracleFree
        (gf2VariableProgram_oracleFree assignmentProgram hassignment)))
    (oracleFree_linkPrograms balancedNatSumProgram_oracleFree
      gf2ZeroTestProgram_oracleFree)

def gf2MonomialRequestFuel (assignmentProgram : NPOracleProgram)
    (assignmentFuel : ℕ → ℕ) (contextCode : ℕ) (monomial : List ℕ) : ℕ :=
  linkFuel (balancedCallProgram (gf2VariableProgram assignmentProgram))
    (nativeInputRequestTreeFuel monomial)
    (balancedCallFuel (gf2VariableProgram assignmentProgram)
      (gf2VariableFuel assignmentFuel)
      (gf2VariableRequests contextCode monomial))

def gf2MonomialSumFuel (assignment : ℕ → Bool) (contextCode : ℕ)
    (monomial : List ℕ) : ℕ :=
  linkFuel gf2ZeroTestProgram
    (balancedNatSumFuel
      (gf2VariableOutputs assignment contextCode monomial))
    gf2ZeroTestFuel

def gf2MonomialFuel (assignmentProgram : NPOracleProgram)
    (assignment : ℕ → Bool) (assignmentFuel : ℕ → ℕ)
    (contextCode : ℕ) (monomial : List ℕ) : ℕ :=
  linkFuel (linkPrograms balancedNatSumProgram gf2ZeroTestProgram)
    (gf2MonomialRequestFuel assignmentProgram assignmentFuel contextCode
      monomial)
    (gf2MonomialSumFuel assignment contextCode monomial)

def gf2MonomialBits (assignment : ℕ → Bool) (contextCode : ℕ)
    (monomial : List ℕ) : ℕ :=
  max 1 <| max (natBitLength contextCode) <|
    max (nativeInputRequestTreeBits contextCode monomial) <|
      max
        (balancedCallRequiredBits (gf2VariableOutput assignment)
          (gf2VariableRequests contextCode monomial))
        (balancedNatSumBits contextCode
          (gf2VariableOutputs assignment contextCode monomial))

theorem run_gf2MonomialProgram
    (assignmentProgram : NPOracleProgram) (assignment : ℕ → Bool)
    (assignmentFuel : ℕ → ℕ) (maximumBits contextCode : ℕ)
    (monomial : List ℕ)
    (hbits : gf2MonomialBits assignment contextCode monomial ≤ maximumBits)
    (hassignment : ∀ code, code ∈ monomial →
      runNPOracleProgram assignmentProgram maximumBits (assignmentFuel code)
          (initialNPOracleState contextCode code) =
        some (boolCode (assignment code))) :
    runNPOracleProgram (gf2MonomialProgram assignmentProgram) maximumBits
        (gf2MonomialFuel assignmentProgram assignment assignmentFuel
          contextCode monomial)
        (initialNPOracleState contextCode (encodeBalancedList monomial)) =
      some (boolCode (monomial.all assignment)) := by
  have hunfold : gf2MonomialBits assignment contextCode monomial =
      max 1 (max (natBitLength contextCode)
        (max (nativeInputRequestTreeBits contextCode monomial)
          (max
            (balancedCallRequiredBits (gf2VariableOutput assignment)
              (gf2VariableRequests contextCode monomial))
            (balancedNatSumBits contextCode
              (gf2VariableOutputs assignment contextCode monomial))))) :=
    rfl
  rw [hunfold] at hbits
  have hpositive : 1 ≤ maximumBits := by omega
  have hcontext : natBitLength contextCode ≤ maximumBits := by omega
  have htreeBits :
      nativeInputRequestTreeBits contextCode monomial ≤ maximumBits := by
    omega
  have hcallBits :
      balancedCallRequiredBits (gf2VariableOutput assignment)
          (gf2VariableRequests contextCode monomial) ≤ maximumBits := by
    omega
  have hsumBits :
      balancedNatSumBits contextCode
          (gf2VariableOutputs assignment contextCode monomial) ≤
        maximumBits := by
    omega
  have hexec : ∀ request, request ∈ gf2VariableRequests contextCode monomial →
      runNPOracleProgram (gf2VariableProgram assignmentProgram) maximumBits
          (gf2VariableFuel assignmentFuel request)
          (initialNPOracleState (Nat.unpair request).1
            (Nat.unpair request).2) =
        some (gf2VariableOutput assignment request) := by
    intro request hrequest
    obtain ⟨code, hcode, hpair⟩ :=
      List.mem_map.mp (by simpa [gf2VariableRequests] using hrequest)
    have hleft :
        (Nat.unpair (nativeInputRequest contextCode code)).1 =
          contextCode := by
      simp [nativeInputRequest]
    have hright :
        (Nat.unpair (nativeInputRequest contextCode code)).2 = code := by
      simp [nativeInputRequest]
    rw [← hpair, hleft, hright]
    exact run_gf2VariableProgram assignmentProgram assignment assignmentFuel
      maximumBits contextCode code hpositive hcontext (hassignment code hcode)
  have hcall :
      runNPOracleProgram
          (balancedCallProgram (gf2VariableProgram assignmentProgram))
          maximumBits
          (balancedCallFuel (gf2VariableProgram assignmentProgram)
            (gf2VariableFuel assignmentFuel)
            (gf2VariableRequests contextCode monomial))
          (initialNPOracleState contextCode
            (encodeBalancedList
              (gf2VariableRequests contextCode monomial))) =
        some
          (encodeBalancedList
            (gf2VariableOutputs assignment contextCode monomial)) :=
    run_balancedCallProgram_from contextCode
      (gf2VariableRequests contextCode monomial)
      (gf2VariableFuel assignmentFuel) (gf2VariableOutput assignment)
      hcallBits hexec
  have hrequests :
      runNPOracleProgram
          (linkPrograms nativeInputRequestTreeProgram
            (balancedCallProgram (gf2VariableProgram assignmentProgram)))
          maximumBits
          (gf2MonomialRequestFuel assignmentProgram assignmentFuel
            contextCode monomial)
          (initialNPOracleState contextCode
            (encodeBalancedList monomial)) =
        some
          (encodeBalancedList
            (gf2VariableOutputs assignment contextCode monomial)) :=
    run_linkPrograms hpositive hcontext
      (run_bits_mono
        (run_nativeInputRequestTreeProgram contextCode monomial) htreeBits)
      hcall
  have hvalue :
      boolCode
          (decide
            ((gf2VariableOutputs assignment contextCode monomial).sum = 0)) =
        boolCode (monomial.all assignment) := by
    rw [all_eq_decide_sum_eq_zero assignment monomial,
      gf2VariableOutputs_eq assignment contextCode monomial]
  have hsum :
      runNPOracleProgram
          (linkPrograms balancedNatSumProgram gf2ZeroTestProgram)
          maximumBits
          (gf2MonomialSumFuel assignment contextCode monomial)
          (initialNPOracleState contextCode
            (encodeBalancedList
              (gf2VariableOutputs assignment contextCode monomial))) =
        some (boolCode (monomial.all assignment)) := by
    rw [← hvalue]
    exact run_linkPrograms hpositive hcontext
      (run_bits_mono
        (run_balancedNatSumProgram contextCode
          (gf2VariableOutputs assignment contextCode monomial))
        hsumBits)
      (run_gf2ZeroTestProgram contextCode maximumBits
        ((gf2VariableOutputs assignment contextCode monomial).sum)
        hpositive)
  exact run_linkPrograms hpositive hcontext hrequests hsum

/-! ## §5 The complete structural polynomial

The polynomial is the balanced list of its monomial codes.  The same request
tree distributes the assignment context over the monomials, and the fixed
balanced parity fold reduces their bits in characteristic two. -/

/-- Machine code of one monomial: the balanced list of its variable codes. -/
def encodedGF2Monomial (monomial : EncodedGF2Monomial) : ℕ :=
  encodeBalancedList monomial

/-- Machine code of a structural polynomial. -/
def encodedStructuralGF2 (polynomial : StructuralGF2Polynomial) : ℕ :=
  encodeBalancedList (polynomial.map encodedGF2Monomial)

/-- Output of one monomial call, as a function of the balanced-call request. -/
def gf2MonomialOutput (assignment : ℕ → Bool) (request : ℕ) : ℕ :=
  boolCode
    (((decodeBalancedList (Nat.unpair request).2).getD []).all assignment)

def gf2MonomialRequests (contextCode : ℕ)
    (polynomial : StructuralGF2Polynomial) : List ℕ :=
  (polynomial.map encodedGF2Monomial).map (nativeInputRequest contextCode)

def gf2MonomialOutputs (assignment : ℕ → Bool) (contextCode : ℕ)
    (polynomial : StructuralGF2Polynomial) : List ℕ :=
  (gf2MonomialRequests contextCode polynomial).map
    (gf2MonomialOutput assignment)

theorem gf2MonomialOutputs_eq
    (assignment : ℕ → Bool) (contextCode : ℕ)
    (polynomial : StructuralGF2Polynomial) :
    gf2MonomialOutputs assignment contextCode polynomial =
      (polynomial.map fun monomial => monomial.all assignment).map
        Bool.toNat := by
  simp [gf2MonomialOutputs, gf2MonomialRequests, gf2MonomialOutput,
    nativeInputRequest, encodedGF2Monomial, boolCode]

private theorem member_le_foldr_max
    {value : ℕ} {values : List ℕ} (hvalue : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => simp at hvalue
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp hvalue with hhead | htail
      · rw [hhead]
        exact le_max_left _ _
      · exact (inductionHypothesis htail).trans (le_max_right _ _)

/-- The monomial stage's outputs are Boolean codes, so
`CanonicalBalancedTraversalParityProgram.taggedParity_eq_sum_mod_two` applies to
them and the balanced-traversal fold reproduces the published `taggedParity`. -/
theorem gf2MonomialOutputs_le_one
    (assignment : ℕ → Bool) (contextCode : ℕ)
    (polynomial : StructuralGF2Polynomial) :
    ∀ value ∈ gf2MonomialOutputs assignment contextCode polynomial, value ≤ 1 := by
  intro value hvalue
  rw [gf2MonomialOutputs_eq] at hvalue
  obtain ⟨entry, _hentry, hcode⟩ := List.mem_map.mp hvalue
  rw [← hcode]
  cases entry <;> simp

@[simp] theorem gf2MonomialOutputs_length
    (assignment : ℕ → Bool) (contextCode : ℕ)
    (polynomial : StructuralGF2Polynomial) :
    (gf2MonomialOutputs assignment contextCode polynomial).length =
      polynomial.length := by
  simp [gf2MonomialOutputs, gf2MonomialRequests]

/-- **The structural `𝔽₂` evaluator.**  Two balanced maps and one parity fold
around the link-time assignment program. -/
def structuralGF2EvaluationProgram (assignmentProgram : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms
    (linkPrograms nativeInputRequestTreeProgram
      (balancedCallProgram (gf2MonomialProgram assignmentProgram)))
    balancedTraversalParityProgram

theorem structuralGF2EvaluationProgram_oracleFree
    (assignmentProgram : NPOracleProgram)
    (hassignment : OracleFree assignmentProgram) :
    OracleFree (structuralGF2EvaluationProgram assignmentProgram) :=
  oracleFree_linkPrograms
    (oracleFree_linkPrograms nativeInputRequestTreeProgram_oracleFree
      (balancedCallProgram_oracleFree
        (gf2MonomialProgram_oracleFree assignmentProgram hassignment)))
    balancedTraversalParityProgram_oracleFree

def gf2MonomialCallFuel (assignmentProgram : NPOracleProgram)
    (assignment : ℕ → Bool) (assignmentFuel : ℕ → ℕ) (request : ℕ) : ℕ :=
  gf2MonomialFuel assignmentProgram assignment assignmentFuel
    (Nat.unpair request).1
    ((decodeBalancedList (Nat.unpair request).2).getD [])

def structuralGF2EvaluationRequestFuel (assignmentProgram : NPOracleProgram)
    (assignment : ℕ → Bool) (assignmentFuel : ℕ → ℕ) (contextCode : ℕ)
    (polynomial : StructuralGF2Polynomial) : ℕ :=
  linkFuel (balancedCallProgram (gf2MonomialProgram assignmentProgram))
    (nativeInputRequestTreeFuel (polynomial.map encodedGF2Monomial))
    (balancedCallFuel (gf2MonomialProgram assignmentProgram)
      (gf2MonomialCallFuel assignmentProgram assignment assignmentFuel)
      (gf2MonomialRequests contextCode polynomial))

def structuralGF2EvaluationFuel (assignmentProgram : NPOracleProgram)
    (assignment : ℕ → Bool) (assignmentFuel : ℕ → ℕ) (contextCode : ℕ)
    (polynomial : StructuralGF2Polynomial) : ℕ :=
  linkFuel balancedTraversalParityProgram
    (structuralGF2EvaluationRequestFuel assignmentProgram assignment
      assignmentFuel contextCode polynomial)
    (balancedTraversalParityFuel
      (gf2MonomialOutputs assignment contextCode polynomial))

def structuralGF2EvaluationBits (assignment : ℕ → Bool) (contextCode : ℕ)
    (polynomial : StructuralGF2Polynomial) : ℕ :=
  max 1 <| max (natBitLength contextCode) <|
    max
      (nativeInputRequestTreeBits contextCode
        (polynomial.map encodedGF2Monomial)) <|
      max
        (balancedCallRequiredBits (gf2MonomialOutput assignment)
          (gf2MonomialRequests contextCode polynomial)) <|
        max
          (balancedTraversalParityBits contextCode
            (gf2MonomialOutputs assignment contextCode polynomial))
          ((polynomial.map
            (gf2MonomialBits assignment contextCode)).foldr max 0)

/-- **Exact structural `𝔽₂` evaluation.**  One machine run on the encoded
polynomial delivers the Boolean code of `evaluateStructuralGF2`; the only
premise is the link-time assignment program's own exact run on each variable
code that occurs. -/
theorem run_structuralGF2EvaluationProgram
    (assignmentProgram : NPOracleProgram) (assignment : ℕ → Bool)
    (assignmentFuel : ℕ → ℕ) (maximumBits contextCode : ℕ)
    (polynomial : StructuralGF2Polynomial)
    (hbits :
      structuralGF2EvaluationBits assignment contextCode polynomial ≤
        maximumBits)
    (hassignment : ∀ monomial, monomial ∈ polynomial →
      ∀ code, code ∈ monomial →
        runNPOracleProgram assignmentProgram maximumBits
            (assignmentFuel code)
            (initialNPOracleState contextCode code) =
          some (boolCode (assignment code))) :
    runNPOracleProgram (structuralGF2EvaluationProgram assignmentProgram)
        maximumBits
        (structuralGF2EvaluationFuel assignmentProgram assignment
          assignmentFuel contextCode polynomial)
        (initialNPOracleState contextCode
          (encodedStructuralGF2 polynomial)) =
      some (boolCode (evaluateStructuralGF2 assignment polynomial)) := by
  have hunfold :
      structuralGF2EvaluationBits assignment contextCode polynomial =
        max 1 (max (natBitLength contextCode)
          (max
            (nativeInputRequestTreeBits contextCode
              (polynomial.map encodedGF2Monomial))
            (max
              (balancedCallRequiredBits (gf2MonomialOutput assignment)
                (gf2MonomialRequests contextCode polynomial))
              (max
                (balancedTraversalParityBits contextCode
                  (gf2MonomialOutputs assignment contextCode polynomial))
                ((polynomial.map
                  (gf2MonomialBits assignment contextCode)).foldr
                    max 0))))) :=
    rfl
  rw [hunfold] at hbits
  have hpositive : 1 ≤ maximumBits := by omega
  have hcontext : natBitLength contextCode ≤ maximumBits := by omega
  have htreeBits :
      nativeInputRequestTreeBits contextCode
          (polynomial.map encodedGF2Monomial) ≤ maximumBits := by
    omega
  have hcallBits :
      balancedCallRequiredBits (gf2MonomialOutput assignment)
          (gf2MonomialRequests contextCode polynomial) ≤ maximumBits := by
    omega
  have hparityBits :
      balancedTraversalParityBits contextCode
          (gf2MonomialOutputs assignment contextCode polynomial) ≤
        maximumBits := by
    omega
  have hmonomialBits : ∀ monomial, monomial ∈ polynomial →
      gf2MonomialBits assignment contextCode monomial ≤ maximumBits := by
    intro monomial hmonomial
    have hmember :
        gf2MonomialBits assignment contextCode monomial ≤
          (polynomial.map
            (gf2MonomialBits assignment contextCode)).foldr max 0 :=
      member_le_foldr_max (List.mem_map_of_mem hmonomial)
    omega
  have hexec : ∀ request,
      request ∈ gf2MonomialRequests contextCode polynomial →
      runNPOracleProgram (gf2MonomialProgram assignmentProgram) maximumBits
          (gf2MonomialCallFuel assignmentProgram assignment assignmentFuel
            request)
          (initialNPOracleState (Nat.unpair request).1
            (Nat.unpair request).2) =
        some (gf2MonomialOutput assignment request) := by
    intro request hrequest
    obtain ⟨monomial, hmonomial, hpair⟩ :=
      List.mem_map.mp
        (by simpa [gf2MonomialRequests, List.map_map] using hrequest)
    have hleft :
        (Nat.unpair
          (nativeInputRequest contextCode
            (encodedGF2Monomial monomial))).1 = contextCode := by
      simp [nativeInputRequest]
    have hright :
        (Nat.unpair
          (nativeInputRequest contextCode
            (encodedGF2Monomial monomial))).2 =
          encodeBalancedList monomial := by
      simp [nativeInputRequest, encodedGF2Monomial]
    have hfuel :
        gf2MonomialCallFuel assignmentProgram assignment assignmentFuel
            (nativeInputRequest contextCode
              (encodedGF2Monomial monomial)) =
          gf2MonomialFuel assignmentProgram assignment assignmentFuel
            contextCode monomial := by
      rw [gf2MonomialCallFuel, hleft, hright]
      simp
    have houtput :
        gf2MonomialOutput assignment
            (nativeInputRequest contextCode
              (encodedGF2Monomial monomial)) =
          boolCode (monomial.all assignment) := by
      rw [gf2MonomialOutput, hright]
      simp
    rw [← hpair, hleft, hright, hfuel, houtput]
    exact run_gf2MonomialProgram assignmentProgram assignment assignmentFuel
      maximumBits contextCode monomial (hmonomialBits monomial hmonomial)
      (hassignment monomial hmonomial)
  have hcall :
      runNPOracleProgram
          (balancedCallProgram (gf2MonomialProgram assignmentProgram))
          maximumBits
          (balancedCallFuel (gf2MonomialProgram assignmentProgram)
            (gf2MonomialCallFuel assignmentProgram assignment assignmentFuel)
            (gf2MonomialRequests contextCode polynomial))
          (initialNPOracleState contextCode
            (encodeBalancedList
              (gf2MonomialRequests contextCode polynomial))) =
        some
          (encodeBalancedList
            (gf2MonomialOutputs assignment contextCode polynomial)) :=
    run_balancedCallProgram_from contextCode
      (gf2MonomialRequests contextCode polynomial)
      (gf2MonomialCallFuel assignmentProgram assignment assignmentFuel)
      (gf2MonomialOutput assignment) hcallBits hexec
  have hrequests :
      runNPOracleProgram
          (linkPrograms nativeInputRequestTreeProgram
            (balancedCallProgram (gf2MonomialProgram assignmentProgram)))
          maximumBits
          (structuralGF2EvaluationRequestFuel assignmentProgram assignment
            assignmentFuel contextCode polynomial)
          (initialNPOracleState contextCode
            (encodedStructuralGF2 polynomial)) =
        some
          (encodeBalancedList
            (gf2MonomialOutputs assignment contextCode polynomial)) :=
    run_linkPrograms hpositive hcontext
      (run_bits_mono
        (run_nativeInputRequestTreeProgram contextCode
          (polynomial.map encodedGF2Monomial)) htreeBits)
      hcall
  have hparity :
      taggedParity (gf2MonomialOutputs assignment contextCode polynomial) =
        boolCode (evaluateStructuralGF2 assignment polynomial) := by
    rw [gf2MonomialOutputs_eq, taggedParity_boolToNat,
      evaluateStructuralGF2_eq_foldl]
    rfl
  have hfold :
      runNPOracleProgram balancedTraversalParityProgram maximumBits
          (balancedTraversalParityFuel
            (gf2MonomialOutputs assignment contextCode polynomial))
          (initialNPOracleState contextCode
            (encodeBalancedList
              (gf2MonomialOutputs assignment contextCode polynomial))) =
        some (boolCode (evaluateStructuralGF2 assignment polynomial)) := by
    rw [← hparity]
    exact run_bits_mono
      (run_balancedTraversalParityProgram_taggedParity contextCode
        (gf2MonomialOutputs assignment contextCode polynomial)
        (gf2MonomialOutputs_le_one assignment contextCode polynomial))
      hparityBits
  exact run_linkPrograms hpositive hcontext hrequests hfold

/-! ## §6 The canonical finite Boolean assignment

Every structural row polynomial in `CanonicalFourfoldRowProgram` is evaluated
at `encodedFiniteBooleanAssignment`, whose out-of-range convention is `false`
rather than a truncation.  The context code carries the population beside the
balanced table of bits, so the range guard reads its bound from the same word
the table came in, and the fixed balanced lookup does the rest. -/

/-- The finite Boolean assignment as one canonical balanced table. -/
def finiteAssignmentTable
    {population : ℕ} (active : Fin population → Bool) : List ℕ :=
  List.ofFn fun index => boolCode (active index)

@[simp] theorem finiteAssignmentTable_length
    {population : ℕ} (active : Fin population → Bool) :
    (finiteAssignmentTable active).length = population := by
  simp [finiteAssignmentTable]

/-- Assignment context: the population beside the balanced table of bits. -/
def finiteAssignmentContext
    {population : ℕ} (active : Fin population → Bool) : ℕ :=
  Nat.pair population (encodeBalancedList (finiteAssignmentTable active))

/-- Range guard output: tag zero selects the balanced lookup on the canonical
lookup request, and any nonzero tag selects the constant-false branch. -/
def finiteAssignmentGuardOutput (population table code : ℕ) : ℕ :=
  if code < population then
    Nat.pair 0 (Nat.pair population (Nat.pair code table))
  else Nat.pair 1 1

def finiteAssignmentGuardProgram : NPOracleProgram :=
  [ .unpairLeft 1 2 1
  , .unpairRight 1 3 2
  , .subtract 2 0 4 3
  , .branchZero 4 8 4
  , .pair 0 3 5 5
  , .pair 2 5 5 6
  , .set 6 0 7
  , .pair 6 5 0 10
  , .set 6 1 9
  , .pair 6 6 0 10
  , .halt 0
  ]

@[simp] theorem finiteAssignmentGuardProgram_oracleFree :
    OracleFree finiteAssignmentGuardProgram := by
  rfl

def finiteAssignmentGuardFuel : ℕ := 9

def finiteAssignmentGuardBits (population table code : ℕ) : ℕ :=
  max (natBitLength (Nat.pair population table)) <|
    max (natBitLength code)
      (natBitLength (finiteAssignmentGuardOutput population table code))

theorem run_finiteAssignmentGuardProgram
    (maximumBits population table code : ℕ)
    (hbits : finiteAssignmentGuardBits population table code ≤ maximumBits) :
    runNPOracleProgram finiteAssignmentGuardProgram maximumBits
        finiteAssignmentGuardFuel
        (initialNPOracleState (Nat.pair population table) code) =
      some (finiteAssignmentGuardOutput population table code) := by
  have hunfold : finiteAssignmentGuardBits population table code =
      max (natBitLength (Nat.pair population table))
        (max (natBitLength code)
          (natBitLength
            (finiteAssignmentGuardOutput population table code))) :=
    rfl
  rw [hunfold] at hbits
  have hcontext : natBitLength (Nat.pair population table) ≤ maximumBits := by
    omega
  have hcodeBits : natBitLength code ≤ maximumBits := by omega
  have houtputBits :
      natBitLength (finiteAssignmentGuardOutput population table code) ≤
        maximumBits := by
    omega
  have hpopulation : natBitLength population ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair population table)).trans hcontext
  have htable : natBitLength table ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair population table)).trans hcontext
  have hdifference : natBitLength (population - code) ≤ maximumBits :=
    (natBitLength_mono (Nat.sub_le population code)).trans hpopulation
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le population)).trans hpopulation
  rw [show finiteAssignmentGuardFuel = 8 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := population) (by rfl) rfl
    (by simp [initialNPOracleState]) hpopulation]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := table) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    htable]
  rw [show 7 = 6 + 1 by omega]
  rw [run_subtract_instruction (value := population - code) (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hdifference]
  rw [show 6 = 5 + 1 by omega]
  rw [run_branchZero_instruction (by rfl) rfl]
  have hregister :
      (((((((initialNPOracleState (Nat.pair population table) code).write 2
        population).jump 1).write 3 table).jump 2).write 4
          (population - code)).jump 3).registers 4 = population - code := by
    simp [NPOracleState.write, NPOracleState.jump]
  rw [hregister]
  by_cases hrange : code < population
  · have hnonzero : population - code ≠ 0 := by omega
    have hpayloadBits :
        natBitLength (Nat.pair population (Nat.pair code table)) ≤
          maximumBits := by
      refine (natBitLength_mono ?_).trans houtputBits
      rw [finiteAssignmentGuardOutput, if_pos hrange]
      exact Nat.right_le_pair 0 (Nat.pair population (Nat.pair code table))
    have hinnerBits : natBitLength (Nat.pair code table) ≤ maximumBits :=
      (natBitLength_mono
        (Nat.right_le_pair population (Nat.pair code table))).trans
          hpayloadBits
    rw [if_neg hnonzero]
    rw [show 5 = 4 + 1 by omega]
    rw [run_pair_instruction (value := Nat.pair code table) (by rfl) rfl
      (by
        simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump]) hinnerBits]
    rw [show 4 = 3 + 1 by omega]
    rw [run_pair_instruction
      (value := Nat.pair population (Nat.pair code table)) (by rfl) rfl
      (by
        simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump]) hpayloadBits]
    rw [show 3 = 2 + 1 by omega]
    rw [run_set_instruction (value := 0) (by rfl) rfl hzeroBits]
    rw [show finiteAssignmentGuardOutput population table code =
        Nat.pair 0 (Nat.pair population (Nat.pair code table)) by
      rw [finiteAssignmentGuardOutput, if_pos hrange]]
    rw [show 2 = 1 + 1 by omega]
    rw [run_pair_instruction
      (value := Nat.pair 0 (Nat.pair population (Nat.pair code table)))
      (by rfl) rfl
      (by
        simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump])
      (by
        rw [show
          natBitLength (Nat.pair 0 (Nat.pair population
            (Nat.pair code table))) =
            natBitLength
              (finiteAssignmentGuardOutput population table code) by
          rw [finiteAssignmentGuardOutput, if_pos hrange]]
        exact houtputBits)]
    exact run_halt_instruction (fuel := 0)
      (value := Nat.pair 0 (Nat.pair population (Nat.pair code table)))
      (by rfl) rfl
      (by
        simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump])
      (by
        rw [show
          natBitLength (Nat.pair 0 (Nat.pair population
            (Nat.pair code table))) =
            natBitLength
              (finiteAssignmentGuardOutput population table code) by
          rw [finiteAssignmentGuardOutput, if_pos hrange]]
        exact houtputBits)
  · have hzero : population - code = 0 := by omega
    have houtput :
        finiteAssignmentGuardOutput population table code =
          Nat.pair 1 1 := by
      rw [finiteAssignmentGuardOutput, if_neg hrange]
    have honeBits : natBitLength 1 ≤ maximumBits := by
      refine (natBitLength_mono ?_).trans houtputBits
      rw [houtput]
      exact Nat.left_le_pair 1 1
    rw [hzero, if_pos rfl]
    rw [show 5 = 4 + 1 by omega]
    rw [run_set_instruction (value := 1) (by rfl) rfl honeBits]
    rw [houtput]
    rw [show 4 = 3 + 1 by omega]
    rw [run_pair_instruction (value := Nat.pair 1 1) (by rfl) rfl
      (by
        simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump])
      (by rw [← houtput]; exact houtputBits)]
    exact run_halt_instruction (fuel := 2) (value := Nat.pair 1 1)
      (by rfl) rfl
      (by
        simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump])
      (by rw [← houtput]; exact houtputBits)

/-! ## §7 The assignment program

Out-of-range codes are `false` by definition of `encodedFiniteBooleanAssignment`
and by the machine's second branch; no truncation or wrap-around is possible. -/

def constantFalseProgram : NPOracleProgram :=
  [ .set 0 0 1
  , .halt 0
  ]

@[simp] theorem constantFalseProgram_oracleFree :
    OracleFree constantFalseProgram := by
  rfl

def constantFalseFuel : ℕ := 2

theorem run_constantFalseProgram
    (inputLength maximumBits code : ℕ) (hpositive : 1 ≤ maximumBits) :
    runNPOracleProgram constantFalseProgram maximumBits constantFalseFuel
        (initialNPOracleState inputLength code) =
      some (boolCode false) := by
  have hzeroBits : natBitLength (boolCode false) ≤ maximumBits :=
    bits_of_boolCode false hpositive
  rw [show constantFalseFuel = 1 + 1 by rfl]
  rw [run_set_instruction (value := boolCode false) (by rfl) rfl hzeroBits]
  exact run_halt_instruction (fuel := 0) (value := boolCode false)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hzeroBits

/-- **The canonical finite Boolean assignment machine.** -/
def encodedFiniteBooleanAssignmentProgram : NPOracleProgram :=
  linkPrograms finiteAssignmentGuardProgram
    (taggedProgramChoice canonicalBalancedLookupProgram constantFalseProgram)

@[simp] theorem encodedFiniteBooleanAssignmentProgram_oracleFree :
    OracleFree encodedFiniteBooleanAssignmentProgram :=
  oracleFree_linkPrograms finiteAssignmentGuardProgram_oracleFree
    (taggedProgramChoice_oracleFree canonicalBalancedLookupProgram
      constantFalseProgram canonicalBalancedLookupProgram_oracleFree
      constantFalseProgram_oracleFree)

def encodedFiniteBooleanAssignmentBranchFuel
    {population : ℕ} (active : Fin population → Bool) (code : ℕ) : ℕ :=
  if code < population then
    balancedLookupFuel (finiteAssignmentTable active) code
  else constantFalseFuel

def encodedFiniteBooleanAssignmentFuel
    {population : ℕ} (active : Fin population → Bool) (code : ℕ) : ℕ :=
  linkFuel
    (taggedProgramChoice canonicalBalancedLookupProgram constantFalseProgram)
    finiteAssignmentGuardFuel
    (taggedProgramChoiceFuel
      (encodedFiniteBooleanAssignmentBranchFuel active code))

def encodedFiniteBooleanAssignmentBits
    {population : ℕ} (active : Fin population → Bool) (code : ℕ) : ℕ :=
  max 1 <|
    max
      (finiteAssignmentGuardBits population
        (encodeBalancedList (finiteAssignmentTable active)) code) <|
      max
        (natBitLength
          (Nat.pair (finiteAssignmentContext active)
            (finiteAssignmentGuardOutput population
              (encodeBalancedList (finiteAssignmentTable active)) code)))
        (balancedLookupMaximumBits (finiteAssignmentTable active) code)

/-- Exact execution of the assignment on one variable code. -/
theorem run_encodedFiniteBooleanAssignmentProgram
    {population : ℕ} (active : Fin population → Bool)
    (maximumBits code : ℕ)
    (hbits : encodedFiniteBooleanAssignmentBits active code ≤ maximumBits) :
    runNPOracleProgram encodedFiniteBooleanAssignmentProgram maximumBits
        (encodedFiniteBooleanAssignmentFuel active code)
        (initialNPOracleState (finiteAssignmentContext active) code) =
      some (boolCode (encodedFiniteBooleanAssignment active code)) := by
  have hunfold : encodedFiniteBooleanAssignmentBits active code =
      max 1
        (max
          (finiteAssignmentGuardBits population
            (encodeBalancedList (finiteAssignmentTable active)) code)
          (max
            (natBitLength
              (Nat.pair (finiteAssignmentContext active)
                (finiteAssignmentGuardOutput population
                  (encodeBalancedList (finiteAssignmentTable active)) code)))
            (balancedLookupMaximumBits (finiteAssignmentTable active)
              code))) :=
    rfl
  rw [hunfold] at hbits
  have hpositive : 1 ≤ maximumBits := by omega
  have hguardBits :
      finiteAssignmentGuardBits population
          (encodeBalancedList (finiteAssignmentTable active)) code ≤
        maximumBits := by
    omega
  have htaggedBits :
      natBitLength
          (Nat.pair (finiteAssignmentContext active)
            (finiteAssignmentGuardOutput population
              (encodeBalancedList (finiteAssignmentTable active)) code)) ≤
        maximumBits := by
    omega
  have hlookupBits :
      balancedLookupMaximumBits (finiteAssignmentTable active) code ≤
        maximumBits := by
    omega
  have hcontextBits :
      natBitLength (finiteAssignmentContext active) ≤ maximumBits := by
    refine (natBitLength_mono ?_).trans htaggedBits
    exact Nat.left_le_pair _ _
  have hguard :
      runNPOracleProgram finiteAssignmentGuardProgram maximumBits
          finiteAssignmentGuardFuel
          (initialNPOracleState (finiteAssignmentContext active) code) =
        some
          (finiteAssignmentGuardOutput population
            (encodeBalancedList (finiteAssignmentTable active)) code) :=
    run_finiteAssignmentGuardProgram maximumBits population
      (encodeBalancedList (finiteAssignmentTable active)) code hguardBits
  have houtputBits :
      natBitLength
          (boolCode (encodedFiniteBooleanAssignment active code)) ≤
        maximumBits :=
    bits_of_boolCode _ hpositive
  by_cases hrange : code < population
  · have hindex : code < (finiteAssignmentTable active).length := by
      rw [finiteAssignmentTable_length]
      exact hrange
    have hpayload :
        finiteAssignmentGuardOutput population
            (encodeBalancedList (finiteAssignmentTable active)) code =
          Nat.pair 0
            (balancedLookupInput (finiteAssignmentTable active) code) := by
      rw [finiteAssignmentGuardOutput, if_pos hrange, balancedLookupInput,
        finiteAssignmentTable_length]
    have hassign :
        encodedFiniteBooleanAssignment active code =
          active ⟨code, hrange⟩ := by
      simp [encodedFiniteBooleanAssignment, hrange]
    have hentry :
        (finiteAssignmentTable active)[code]'hindex =
          boolCode (encodedFiniteBooleanAssignment active code) := by
      rw [hassign]
      simp [finiteAssignmentTable]
    have hlookup :
        runNPOracleProgram canonicalBalancedLookupProgram maximumBits
            (encodedFiniteBooleanAssignmentBranchFuel active code)
            (initialNPOracleState (finiteAssignmentContext active)
              (balancedLookupInput (finiteAssignmentTable active) code)) =
          some (boolCode (encodedFiniteBooleanAssignment active code)) := by
      rw [encodedFiniteBooleanAssignmentBranchFuel, if_pos hrange, ← hentry]
      exact run_bits_mono
        (run_canonicalBalancedLookupProgram (finiteAssignmentTable active)
          code (finiteAssignmentContext active) hindex)
        hlookupBits
    have hchoice :
        runNPOracleProgram
            (taggedProgramChoice canonicalBalancedLookupProgram
              constantFalseProgram)
            maximumBits
            (taggedProgramChoiceFuel
              (encodedFiniteBooleanAssignmentBranchFuel active code))
            (initialNPOracleState (finiteAssignmentContext active)
              (finiteAssignmentGuardOutput population
                (encodeBalancedList (finiteAssignmentTable active))
                code)) =
          some (boolCode (encodedFiniteBooleanAssignment active code)) := by
      rw [hpayload]
      exact run_taggedProgramChoice_zero canonicalBalancedLookupProgram
        constantFalseProgram (finiteAssignmentContext active)
        (balancedLookupInput (finiteAssignmentTable active) code)
        maximumBits
        (encodedFiniteBooleanAssignmentBranchFuel active code)
        (boolCode (encodedFiniteBooleanAssignment active code))
        (by rw [← hpayload]; exact htaggedBits) hlookup houtputBits
    exact run_linkPrograms hpositive hcontextBits hguard hchoice
  · have hpayload :
        finiteAssignmentGuardOutput population
            (encodeBalancedList (finiteAssignmentTable active)) code =
          Nat.pair 1 1 := by
      rw [finiteAssignmentGuardOutput, if_neg hrange]
    have hvalue :
        boolCode (encodedFiniteBooleanAssignment active code) =
          boolCode false := by
      rw [encodedFiniteBooleanAssignment, dif_neg hrange]
    have hbranch :
        runNPOracleProgram constantFalseProgram maximumBits
            (encodedFiniteBooleanAssignmentBranchFuel active code)
            (initialNPOracleState (finiteAssignmentContext active) 1) =
          some (boolCode (encodedFiniteBooleanAssignment active code)) := by
      rw [encodedFiniteBooleanAssignmentBranchFuel, if_neg hrange, hvalue]
      exact run_constantFalseProgram (finiteAssignmentContext active)
        maximumBits 1 hpositive
    have hchoice :
        runNPOracleProgram
            (taggedProgramChoice canonicalBalancedLookupProgram
              constantFalseProgram)
            maximumBits
            (taggedProgramChoiceFuel
              (encodedFiniteBooleanAssignmentBranchFuel active code))
            (initialNPOracleState (finiteAssignmentContext active)
              (finiteAssignmentGuardOutput population
                (encodeBalancedList (finiteAssignmentTable active))
                code)) =
          some (boolCode (encodedFiniteBooleanAssignment active code)) := by
      rw [hpayload]
      exact run_taggedProgramChoice_nonzero canonicalBalancedLookupProgram
        constantFalseProgram (finiteAssignmentContext active) 1 1
        maximumBits
        (encodedFiniteBooleanAssignmentBranchFuel active code)
        (boolCode (encodedFiniteBooleanAssignment active code))
        (by omega) (by rw [← hpayload]; exact htaggedBits) hbranch
        houtputBits
    exact run_linkPrograms hpositive hcontextBits hguard hchoice

/-! ## §8 The closed evaluator

Composing §5 with §7 leaves no program parameter: one fixed oracle-free
machine evaluates any structural polynomial against any finite Boolean
assignment table, with closed width and fuel envelopes. -/

def encodedFiniteBooleanGF2Program : NPOracleProgram :=
  structuralGF2EvaluationProgram encodedFiniteBooleanAssignmentProgram

@[simp] theorem encodedFiniteBooleanGF2Program_oracleFree :
    OracleFree encodedFiniteBooleanGF2Program :=
  structuralGF2EvaluationProgram_oracleFree
    encodedFiniteBooleanAssignmentProgram
    encodedFiniteBooleanAssignmentProgram_oracleFree

def encodedFiniteBooleanGF2Fuel
    {population : ℕ} (active : Fin population → Bool)
    (polynomial : StructuralGF2Polynomial) : ℕ :=
  structuralGF2EvaluationFuel encodedFiniteBooleanAssignmentProgram
    (encodedFiniteBooleanAssignment active)
    (encodedFiniteBooleanAssignmentFuel active)
    (finiteAssignmentContext active) polynomial

def encodedFiniteBooleanGF2Bits
    {population : ℕ} (active : Fin population → Bool)
    (polynomial : StructuralGF2Polynomial) : ℕ :=
  max
    (structuralGF2EvaluationBits (encodedFiniteBooleanAssignment active)
      (finiteAssignmentContext active) polynomial)
    ((polynomial.map fun monomial =>
      (monomial.map (encodedFiniteBooleanAssignmentBits active)).foldr
        max 0).foldr max 0)

/-- **Exact closed structural `𝔽₂` evaluation.**  One fixed oracle-free
program computes `evaluateStructuralGF2` at the canonical finite Boolean
assignment, from the encoded polynomial and the encoded assignment table. -/
theorem run_encodedFiniteBooleanGF2Program
    {population : ℕ} (active : Fin population → Bool)
    (maximumBits : ℕ) (polynomial : StructuralGF2Polynomial)
    (hbits : encodedFiniteBooleanGF2Bits active polynomial ≤ maximumBits) :
    runNPOracleProgram encodedFiniteBooleanGF2Program maximumBits
        (encodedFiniteBooleanGF2Fuel active polynomial)
        (initialNPOracleState (finiteAssignmentContext active)
          (encodedStructuralGF2 polynomial)) =
      some
        (boolCode
          (evaluateStructuralGF2 (encodedFiniteBooleanAssignment active)
            polynomial)) := by
  have hunfold : encodedFiniteBooleanGF2Bits active polynomial =
      max
        (structuralGF2EvaluationBits (encodedFiniteBooleanAssignment active)
          (finiteAssignmentContext active) polynomial)
        ((polynomial.map fun monomial =>
          (monomial.map (encodedFiniteBooleanAssignmentBits active)).foldr
            max 0).foldr max 0) :=
    rfl
  rw [hunfold] at hbits
  have hevaluationBits :
      structuralGF2EvaluationBits (encodedFiniteBooleanAssignment active)
          (finiteAssignmentContext active) polynomial ≤ maximumBits := by
    omega
  have hassignment : ∀ monomial, monomial ∈ polynomial →
      ∀ code, code ∈ monomial →
        runNPOracleProgram encodedFiniteBooleanAssignmentProgram maximumBits
            (encodedFiniteBooleanAssignmentFuel active code)
            (initialNPOracleState (finiteAssignmentContext active) code) =
          some
            (boolCode (encodedFiniteBooleanAssignment active code)) := by
    intro monomial hmonomial code hcode
    have hinner :
        encodedFiniteBooleanAssignmentBits active code ≤
          (monomial.map (encodedFiniteBooleanAssignmentBits active)).foldr
            max 0 :=
      member_le_foldr_max (List.mem_map_of_mem hcode)
    have houter :
        (monomial.map (encodedFiniteBooleanAssignmentBits active)).foldr
            max 0 ≤
          (polynomial.map fun candidate =>
            (candidate.map
              (encodedFiniteBooleanAssignmentBits active)).foldr max 0).foldr
              max 0 :=
      member_le_foldr_max (List.mem_map_of_mem hmonomial)
    exact run_encodedFiniteBooleanAssignmentProgram active maximumBits code
      (by omega)
  exact run_structuralGF2EvaluationProgram
    encodedFiniteBooleanAssignmentProgram
    (encodedFiniteBooleanAssignment active)
    (encodedFiniteBooleanAssignmentFuel active) maximumBits
    (finiteAssignmentContext active) polynomial hevaluationBits hassignment

/-! ## §9 The symmetric canonical row body

`CanonicalFourfoldRowProgram` already proves that the symmetric row is the
structural polynomial evaluated at the shared residual assignment.  Composing
that identification with §8 executes the row body itself: the machine consumes
only the residual table and the row polynomial, and no stage re-derives the
occurrence pool, the live set, or the circuit masks. -/

/-- The shared residual-variable assignment of one symmetric row. -/
def symmetricRowResidualAssignment
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale : ℕ) (input : BitInput request.q) :
    Fin (symmetricFourfoldOccurrences request).length → Bool :=
  fun index =>
    occurrenceResidualVariable (symmetricFourfoldOccurrences request)
      (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
      input index

/-- Exact execution of one symmetric row body from its residual table and its
structural row polynomial. -/
theorem run_encodedFiniteBooleanGF2Program_symmetricFourfoldRow
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator maximumBits : ℕ) (input : BitInput request.q)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator)
    (constantOffset : Fin request.circuits.length → ℕ)
    (hoffset : ∀ circuitIndex,
      constantOffset circuitIndex =
        occurrenceResidualConstantCount
          (symmetricFourfoldOccurrences request) liveScale input
          (symmetricCircuitMask request circuitIndex))
    (hbits :
      encodedFiniteBooleanGF2Bits
          (symmetricRowResidualAssignment request liveScale input)
          (structuralCanonicalSymmetricFourfoldRow request liveScale
            denominator sample constantOffset) ≤
        maximumBits) :
    runNPOracleProgram encodedFiniteBooleanGF2Program maximumBits
        (encodedFiniteBooleanGF2Fuel
          (symmetricRowResidualAssignment request liveScale input)
          (structuralCanonicalSymmetricFourfoldRow request liveScale
            denominator sample constantOffset))
        (initialNPOracleState
          (finiteAssignmentContext
            (symmetricRowResidualAssignment request liveScale input))
          (encodedStructuralGF2
            (structuralCanonicalSymmetricFourfoldRow request liveScale
              denominator sample constantOffset))) =
      some
        (boolCode
          (executableCanonicalSymmetricFourfoldRow request liveScale
            denominator input sample)) := by
  have hrow :
      evaluateStructuralGF2
          (encodedFiniteBooleanAssignment
            (symmetricRowResidualAssignment request liveScale input))
          (structuralCanonicalSymmetricFourfoldRow request liveScale
            denominator sample constantOffset) =
        executableCanonicalSymmetricFourfoldRow request liveScale
          denominator input sample :=
    evaluateStructuralCanonicalSymmetricFourfoldRow request liveScale
      denominator input sample constantOffset hoffset
  rw [← hrow]
  exact run_encodedFiniteBooleanGF2Program
    (symmetricRowResidualAssignment request liveScale input) maximumBits
    (structuralCanonicalSymmetricFourfoldRow request liveScale denominator
      sample constantOffset)
    hbits

/-- The same execution in the shape the published row evaluator consumes:
the decoded seed and the canonical input code. -/
theorem run_encodedFiniteBooleanGF2Program_evaluateCanonicalSymmetricRow
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale targetDenominator rowIndex maximumBits : ℕ)
    (input : BitInput request.q)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale
      (symmetricListDenominator request targetDenominator))
    (hsample :
      decodeNormalizedOccurrenceListSeed
          (symmetricFourfoldOccurrences request) liveScale
          (symmetricListDenominator request targetDenominator) rowIndex =
        some sample)
    (constantOffset : Fin request.circuits.length → ℕ)
    (hoffset : ∀ circuitIndex,
      constantOffset circuitIndex =
        occurrenceResidualConstantCount
          (symmetricFourfoldOccurrences request) liveScale input
          (symmetricCircuitMask request circuitIndex))
    (hbits :
      encodedFiniteBooleanGF2Bits
          (symmetricRowResidualAssignment request liveScale input)
          (structuralCanonicalSymmetricFourfoldRow request liveScale
            (symmetricListDenominator request targetDenominator) sample
            constantOffset) ≤
        maximumBits) :
    runNPOracleProgram encodedFiniteBooleanGF2Program maximumBits
        (encodedFiniteBooleanGF2Fuel
          (symmetricRowResidualAssignment request liveScale input)
          (structuralCanonicalSymmetricFourfoldRow request liveScale
            (symmetricListDenominator request targetDenominator) sample
            constantOffset))
        (initialNPOracleState
          (finiteAssignmentContext
            (symmetricRowResidualAssignment request liveScale input))
          (encodedStructuralGF2
            (structuralCanonicalSymmetricFourfoldRow request liveScale
              (symmetricListDenominator request targetDenominator) sample
              constantOffset))) =
      some
        (boolCode
          (evaluateCanonicalSymmetricFourfoldRow request liveScale
            targetDenominator rowIndex (encodeBitInput input))) := by
  have hvalue :
      evaluateCanonicalSymmetricFourfoldRow request liveScale
          targetDenominator rowIndex (encodeBitInput input) =
        executableCanonicalSymmetricFourfoldRow request liveScale
          (symmetricListDenominator request targetDenominator) input
          sample := by
    unfold evaluateCanonicalSymmetricFourfoldRow
    dsimp only
    rw [hsample, rowBitInputOfCode_encode]
  rw [hvalue]
  exact run_encodedFiniteBooleanGF2Program_symmetricFourfoldRow request
    liveScale (symmetricListDenominator request targetDenominator)
    maximumBits input sample constantOffset hoffset hbits

/-! ## §10 The row evaluator around one link-time row-data producer

The evaluator's ABI is the row handoff.  Exactly one link-time program
remains: the producer that turns that handoff into the pair
`(assignment context, encoded row polynomial)`.  Everything after it — the
context switch into the closed evaluator of §8 and the evaluation itself — is
executed here with closed width and fuel envelopes. -/

def structuralRowEvaluatorProgram (rowDataProgram : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms rowDataProgram
    (nativeCallProgram encodedFiniteBooleanGF2Program)

theorem structuralRowEvaluatorProgram_oracleFree
    (rowDataProgram : NPOracleProgram) (hdata : OracleFree rowDataProgram) :
    OracleFree (structuralRowEvaluatorProgram rowDataProgram) :=
  oracleFree_linkPrograms hdata
    (nativeCallProgram_oracleFree encodedFiniteBooleanGF2Program_oracleFree)

def structuralRowEvaluatorFuel
    {population : ℕ} (dataFuel : ℕ) (active : Fin population → Bool)
    (polynomial : StructuralGF2Polynomial) : ℕ :=
  linkFuel (nativeCallProgram encodedFiniteBooleanGF2Program) dataFuel
    (nativeCallFuel encodedFiniteBooleanGF2Program
      (encodedFiniteBooleanGF2Fuel active polynomial)
      (finiteAssignmentContext active) (encodedStructuralGF2 polynomial))

def structuralRowEvaluatorBits
    {population : ℕ} (inputLength : ℕ) (active : Fin population → Bool)
    (polynomial : StructuralGF2Polynomial) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    nativeCallBits inputLength (finiteAssignmentContext active)
      (encodedStructuralGF2 polynomial)
      (boolCode
        (evaluateStructuralGF2 (encodedFiniteBooleanAssignment active)
          polynomial))
      (encodedFiniteBooleanGF2Bits active polynomial)

/-- Exact execution of the row evaluator from one row-data producer run. -/
theorem run_structuralRowEvaluatorProgram
    (rowDataProgram : NPOracleProgram) {population : ℕ}
    (active : Fin population → Bool) (polynomial : StructuralGF2Polynomial)
    (maximumBits inputLength handoff dataFuel : ℕ)
    (hbits :
      structuralRowEvaluatorBits inputLength active polynomial ≤ maximumBits)
    (hdata :
      runNPOracleProgram rowDataProgram maximumBits dataFuel
          (initialNPOracleState inputLength handoff) =
        some
          (nativeInputRequest (finiteAssignmentContext active)
            (encodedStructuralGF2 polynomial))) :
    runNPOracleProgram (structuralRowEvaluatorProgram rowDataProgram)
        maximumBits
        (structuralRowEvaluatorFuel dataFuel active polynomial)
        (initialNPOracleState inputLength handoff) =
      some
        (boolCode
          (evaluateStructuralGF2 (encodedFiniteBooleanAssignment active)
            polynomial)) := by
  have hunfold :
      structuralRowEvaluatorBits inputLength active polynomial =
        max 1
          (max (natBitLength inputLength)
            (nativeCallBits inputLength (finiteAssignmentContext active)
              (encodedStructuralGF2 polynomial)
              (boolCode
                (evaluateStructuralGF2
                  (encodedFiniteBooleanAssignment active) polynomial))
              (encodedFiniteBooleanGF2Bits active polynomial))) :=
    rfl
  rw [hunfold] at hbits
  have hpositive : 1 ≤ maximumBits := by omega
  have hlength : natBitLength inputLength ≤ maximumBits := by omega
  have hcallBits :
      nativeCallBits inputLength (finiteAssignmentContext active)
          (encodedStructuralGF2 polynomial)
          (boolCode
            (evaluateStructuralGF2 (encodedFiniteBooleanAssignment active)
              polynomial))
          (encodedFiniteBooleanGF2Bits active polynomial) ≤ maximumBits := by
    omega
  have hcallee :
      runNPOracleProgram encodedFiniteBooleanGF2Program
          (encodedFiniteBooleanGF2Bits active polynomial)
          (encodedFiniteBooleanGF2Fuel active polynomial)
          (initialNPOracleState (finiteAssignmentContext active)
            (encodedStructuralGF2 polynomial)) =
        some
          (boolCode
            (evaluateStructuralGF2 (encodedFiniteBooleanAssignment active)
              polynomial)) :=
    run_encodedFiniteBooleanGF2Program active
      (encodedFiniteBooleanGF2Bits active polynomial) polynomial
      (Nat.le_refl _)
  exact run_linkPrograms hpositive hlength hdata
    (run_bits_mono
      (run_nativeCallProgram encodedFiniteBooleanGF2Program inputLength
        (finiteAssignmentContext active) (encodedStructuralGF2 polynomial)
        (boolCode
          (evaluateStructuralGF2 (encodedFiniteBooleanAssignment active)
            polynomial))
        (encodedFiniteBooleanGF2Bits active polynomial)
        (encodedFiniteBooleanGF2Fuel active polynomial) hcallee)
      hcallBits)

/-! ## §11 The symmetric row evaluator in the published shape

This is the `hevaluator` premise of `run_fourfoldRowModeDispatchProgram_
symmetric` with one remaining link-time obligation: the row-data producer on
the row handoff. -/

theorem run_structuralRowEvaluatorProgram_symmetricFourfoldRow
    (rowDataProgram : NPOracleProgram)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale
      (symmetricListDenominator request
        (fixedTargetDenominator accuracyExponent request.q)))
    (hsample :
      decodeNormalizedOccurrenceListSeed
          (symmetricFourfoldOccurrences request) liveScale
          (symmetricListDenominator request
            (fixedTargetDenominator accuracyExponent request.q)) rowIndex =
        some sample)
    (constantOffset : Fin request.circuits.length → ℕ)
    (hoffset : ∀ circuitIndex,
      constantOffset circuitIndex =
        occurrenceResidualConstantCount
          (symmetricFourfoldOccurrences request) liveScale input
          (symmetricCircuitMask request circuitIndex))
    (maximumBits handoff dataFuel : ℕ)
    (hbits :
      structuralRowEvaluatorBits request.q
          (symmetricRowResidualAssignment request liveScale input)
          (structuralCanonicalSymmetricFourfoldRow request liveScale
            (symmetricListDenominator request
              (fixedTargetDenominator accuracyExponent request.q))
            sample constantOffset) ≤
        maximumBits)
    (hdata :
      runNPOracleProgram rowDataProgram maximumBits dataFuel
          (initialNPOracleState request.q handoff) =
        some
          (nativeInputRequest
            (finiteAssignmentContext
              (symmetricRowResidualAssignment request liveScale input))
            (encodedStructuralGF2
              (structuralCanonicalSymmetricFourfoldRow request liveScale
                (symmetricListDenominator request
                  (fixedTargetDenominator accuracyExponent request.q))
                sample constantOffset)))) :
    runNPOracleProgram (structuralRowEvaluatorProgram rowDataProgram)
        maximumBits
        (structuralRowEvaluatorFuel dataFuel
          (symmetricRowResidualAssignment request liveScale input)
          (structuralCanonicalSymmetricFourfoldRow request liveScale
            (symmetricListDenominator request
              (fixedTargetDenominator accuracyExponent request.q))
            sample constantOffset))
        (initialNPOracleState request.q handoff) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (symmetricFourfoldRowRequest request rowIndex input))) := by
  have hdispatch :
      evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
          (symmetricFourfoldRowRequest request rowIndex input) =
        evaluateCanonicalSymmetricFourfoldRow request liveScale
          (fixedTargetDenominator accuracyExponent request.q) rowIndex
          (encodeBitInput input) :=
    evaluateCanonicalFourfoldRow_symmetric algorithm liveScale
      accuracyExponent request rowIndex input
  have hseed :
      evaluateCanonicalSymmetricFourfoldRow request liveScale
          (fixedTargetDenominator accuracyExponent request.q) rowIndex
          (encodeBitInput input) =
        executableCanonicalSymmetricFourfoldRow request liveScale
          (symmetricListDenominator request
            (fixedTargetDenominator accuracyExponent request.q))
          input sample := by
    unfold evaluateCanonicalSymmetricFourfoldRow
    dsimp only
    rw [hsample, rowBitInputOfCode_encode]
  have hrow :
      evaluateStructuralGF2
          (encodedFiniteBooleanAssignment
            (symmetricRowResidualAssignment request liveScale input))
          (structuralCanonicalSymmetricFourfoldRow request liveScale
            (symmetricListDenominator request
              (fixedTargetDenominator accuracyExponent request.q))
            sample constantOffset) =
        executableCanonicalSymmetricFourfoldRow request liveScale
          (symmetricListDenominator request
            (fixedTargetDenominator accuracyExponent request.q))
          input sample :=
    evaluateStructuralCanonicalSymmetricFourfoldRow request liveScale
      (symmetricListDenominator request
        (fixedTargetDenominator accuracyExponent request.q))
      input sample constantOffset hoffset
  rw [hdispatch, hseed, ← hrow]
  exact run_structuralRowEvaluatorProgram rowDataProgram
    (symmetricRowResidualAssignment request liveScale input)
    (structuralCanonicalSymmetricFourfoldRow request liveScale
      (symmetricListDenominator request
        (fixedTargetDenominator accuracyExponent request.q))
      sample constantOffset)
    maximumBits request.q handoff dataFuel hbits hdata

/-! ## §12 Splitting the row data into two independent producers

The two halves of the row data — the residual assignment table and the row
polynomial — are read from the same handoff and are otherwise unrelated.  The
verified fork runs both on that one handoff and emits exactly the pair the
native call of §10 consumes. -/

def structuralRowDataProgram
    (tableProgram polynomialProgram : NPOracleProgram) : NPOracleProgram :=
  forkCallProgram tableProgram polynomialProgram

theorem structuralRowDataProgram_oracleFree
    (tableProgram polynomialProgram : NPOracleProgram)
    (htable : OracleFree tableProgram)
    (hpolynomial : OracleFree polynomialProgram) :
    OracleFree (structuralRowDataProgram tableProgram polynomialProgram) :=
  forkCallProgram_oracleFree tableProgram polynomialProgram htable
    hpolynomial

def structuralRowDataFuel
    (tableProgram polynomialProgram : NPOracleProgram)
    (tableFuel polynomialFuel : ℕ) : ℕ :=
  forkCallFuel tableProgram polynomialProgram tableFuel polynomialFuel

def structuralRowDataBits
    {population : ℕ} (inputLength handoff tableBits polynomialBits : ℕ)
    (active : Fin population → Bool)
    (polynomial : StructuralGF2Polynomial) : ℕ :=
  forkCallBits inputLength handoff tableBits polynomialBits
    (finiteAssignmentContext active) (encodedStructuralGF2 polynomial)

theorem run_structuralRowDataProgram
    (tableProgram polynomialProgram : NPOracleProgram) {population : ℕ}
    (active : Fin population → Bool) (polynomial : StructuralGF2Polynomial)
    (inputLength handoff tableBits polynomialBits tableFuel
      polynomialFuel : ℕ)
    (htable :
      runNPOracleProgram tableProgram tableBits tableFuel
          (initialNPOracleState inputLength handoff) =
        some (finiteAssignmentContext active))
    (hpolynomial :
      runNPOracleProgram polynomialProgram polynomialBits polynomialFuel
          (initialNPOracleState inputLength handoff) =
        some (encodedStructuralGF2 polynomial)) :
    runNPOracleProgram
        (structuralRowDataProgram tableProgram polynomialProgram)
        (structuralRowDataBits inputLength handoff tableBits polynomialBits
          active polynomial)
        (structuralRowDataFuel tableProgram polynomialProgram tableFuel
          polynomialFuel)
        (initialNPOracleState inputLength handoff) =
      some
        (nativeInputRequest (finiteAssignmentContext active)
          (encodedStructuralGF2 polynomial)) :=
  run_forkCallProgram tableProgram polynomialProgram inputLength handoff
    tableBits polynomialBits tableFuel polynomialFuel
    (finiteAssignmentContext active) (encodedStructuralGF2 polynomial)
    htable hpolynomial

/-! ## §13 The published row evaluators over two producers

Everything below the two producers is now compiled: these are the
`hevaluator` premises of `run_fourfoldRowModeDispatchProgram_symmetric` and
`run_fourfoldRowModeDispatchProgram_threshold` with exactly two remaining
link-time obligations per family. -/

def structuralForkRowEvaluatorProgram
    (tableProgram polynomialProgram : NPOracleProgram) : NPOracleProgram :=
  structuralRowEvaluatorProgram
    (structuralRowDataProgram tableProgram polynomialProgram)

theorem structuralForkRowEvaluatorProgram_oracleFree
    (tableProgram polynomialProgram : NPOracleProgram)
    (htable : OracleFree tableProgram)
    (hpolynomial : OracleFree polynomialProgram) :
    OracleFree (structuralForkRowEvaluatorProgram tableProgram polynomialProgram) :=
  structuralRowEvaluatorProgram_oracleFree
    (structuralRowDataProgram tableProgram polynomialProgram)
    (structuralRowDataProgram_oracleFree tableProgram polynomialProgram
      htable hpolynomial)

def structuralForkRowEvaluatorFuel
    {population : ℕ} (tableProgram polynomialProgram : NPOracleProgram)
    (tableFuel polynomialFuel : ℕ) (active : Fin population → Bool)
    (polynomial : StructuralGF2Polynomial) : ℕ :=
  structuralRowEvaluatorFuel
    (structuralRowDataFuel tableProgram polynomialProgram tableFuel
      polynomialFuel)
    active polynomial

def structuralForkRowEvaluatorBits
    {population : ℕ} (inputLength handoff tableBits polynomialBits : ℕ)
    (active : Fin population → Bool)
    (polynomial : StructuralGF2Polynomial) : ℕ :=
  max (structuralRowEvaluatorBits inputLength active polynomial)
    (structuralRowDataBits inputLength handoff tableBits polynomialBits
      active polynomial)

theorem run_structuralForkRowEvaluatorProgram_symmetric
    (tableProgram polynomialProgram : NPOracleProgram)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale
      (symmetricListDenominator request
        (fixedTargetDenominator accuracyExponent request.q)))
    (hsample :
      decodeNormalizedOccurrenceListSeed
          (symmetricFourfoldOccurrences request) liveScale
          (symmetricListDenominator request
            (fixedTargetDenominator accuracyExponent request.q)) rowIndex =
        some sample)
    (constantOffset : Fin request.circuits.length → ℕ)
    (hoffset : ∀ circuitIndex,
      constantOffset circuitIndex =
        occurrenceResidualConstantCount
          (symmetricFourfoldOccurrences request) liveScale input
          (symmetricCircuitMask request circuitIndex))
    (maximumBits handoff tableBits polynomialBits tableFuel
      polynomialFuel : ℕ)
    (hbits :
      structuralForkRowEvaluatorBits request.q handoff tableBits polynomialBits
          (symmetricRowResidualAssignment request liveScale input)
          (structuralCanonicalSymmetricFourfoldRow request liveScale
            (symmetricListDenominator request
              (fixedTargetDenominator accuracyExponent request.q))
            sample constantOffset) ≤
        maximumBits)
    (htable :
      runNPOracleProgram tableProgram tableBits tableFuel
          (initialNPOracleState request.q handoff) =
        some
          (finiteAssignmentContext
            (symmetricRowResidualAssignment request liveScale input)))
    (hpolynomial :
      runNPOracleProgram polynomialProgram polynomialBits polynomialFuel
          (initialNPOracleState request.q handoff) =
        some
          (encodedStructuralGF2
            (structuralCanonicalSymmetricFourfoldRow request liveScale
              (symmetricListDenominator request
                (fixedTargetDenominator accuracyExponent request.q))
              sample constantOffset))) :
    runNPOracleProgram
        (structuralForkRowEvaluatorProgram tableProgram polynomialProgram)
        maximumBits
        (structuralForkRowEvaluatorFuel tableProgram polynomialProgram tableFuel
          polynomialFuel
          (symmetricRowResidualAssignment request liveScale input)
          (structuralCanonicalSymmetricFourfoldRow request liveScale
            (symmetricListDenominator request
              (fixedTargetDenominator accuracyExponent request.q))
            sample constantOffset))
        (initialNPOracleState request.q handoff) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (symmetricFourfoldRowRequest request rowIndex input))) := by
  have hunfold :
      structuralForkRowEvaluatorBits request.q handoff tableBits polynomialBits
          (symmetricRowResidualAssignment request liveScale input)
          (structuralCanonicalSymmetricFourfoldRow request liveScale
            (symmetricListDenominator request
              (fixedTargetDenominator accuracyExponent request.q))
            sample constantOffset) =
        max
          (structuralRowEvaluatorBits request.q
            (symmetricRowResidualAssignment request liveScale input)
            (structuralCanonicalSymmetricFourfoldRow request liveScale
              (symmetricListDenominator request
                (fixedTargetDenominator accuracyExponent request.q))
              sample constantOffset))
          (structuralRowDataBits request.q handoff tableBits polynomialBits
            (symmetricRowResidualAssignment request liveScale input)
            (structuralCanonicalSymmetricFourfoldRow request liveScale
              (symmetricListDenominator request
                (fixedTargetDenominator accuracyExponent request.q))
              sample constantOffset)) :=
    rfl
  rw [hunfold] at hbits
  have hevaluatorBits :
      structuralRowEvaluatorBits request.q
          (symmetricRowResidualAssignment request liveScale input)
          (structuralCanonicalSymmetricFourfoldRow request liveScale
            (symmetricListDenominator request
              (fixedTargetDenominator accuracyExponent request.q))
            sample constantOffset) ≤
        maximumBits := by
    omega
  have hdataBits :
      structuralRowDataBits request.q handoff tableBits polynomialBits
          (symmetricRowResidualAssignment request liveScale input)
          (structuralCanonicalSymmetricFourfoldRow request liveScale
            (symmetricListDenominator request
              (fixedTargetDenominator accuracyExponent request.q))
            sample constantOffset) ≤
        maximumBits := by
    omega
  exact run_structuralRowEvaluatorProgram_symmetricFourfoldRow
    (structuralRowDataProgram tableProgram polynomialProgram) algorithm
    request liveScale accuracyExponent rowIndex input sample hsample
    constantOffset hoffset maximumBits handoff
    (structuralRowDataFuel tableProgram polynomialProgram tableFuel
      polynomialFuel)
    hevaluatorBits
    (run_bits_mono
      (run_structuralRowDataProgram tableProgram polynomialProgram
        (symmetricRowResidualAssignment request liveScale input)
        (structuralCanonicalSymmetricFourfoldRow request liveScale
          (symmetricListDenominator request
            (fixedTargetDenominator accuracyExponent request.q))
          sample constantOffset)
        request.q handoff tableBits polynomialBits tableFuel polynomialFuel
        htable hpolynomial)
      hdataBits)

/-! ## §14 The threshold twin

The threshold family differs only in its occurrence pool, its mixed-radix
sample, and its residual offsets; the evaluator and both closures above are
family-neutral. -/

/-- The shared residual-variable assignment of one threshold row. -/
def thresholdRowResidualAssignment
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale : ℕ) (input : BitInput request.q) :
    Fin (thresholdFourfoldOccurrences request).length → Bool :=
  fun index =>
    occurrenceResidualVariable (thresholdFourfoldOccurrences request)
      (normalizedLiveSet (thresholdFourfoldOccurrences request) liveScale)
      input index

theorem run_structuralRowEvaluatorProgram_thresholdFourfoldRow
    (rowDataProgram : NPOracleProgram)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q)
    (sample :
      PrimeIndex
          (thresholdPrimeCutoff algorithm request
            (thresholdPrimeUnionDenominator algorithm request
              (fixedTargetDenominator accuracyExponent request.q))) ×
        NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences request)
          liveScale
          (thresholdListUnionDenominator algorithm request
            (fixedTargetDenominator accuracyExponent request.q)))
    (hsample :
      decodePrimeListSample
          (cutoff :=
            thresholdPrimeCutoff algorithm request
              (thresholdPrimeUnionDenominator algorithm request
                (fixedTargetDenominator accuracyExponent request.q)))
          (thresholdFourfoldOccurrences request) liveScale
          (thresholdListUnionDenominator algorithm request
            (fixedTargetDenominator accuracyExponent request.q)) rowIndex =
        some sample)
    (residualOffset : ThresholdChildSelection algorithm request → ℕ)
    (hoffset : ∀ selection,
      residualOffset selection =
        modularResidualOffset (thresholdFourfoldOccurrences request)
          liveScale input
          (thresholdSelectionEquation algorithm request selection)
          sample.1.val)
    (maximumBits handoff dataFuel : ℕ)
    (hbits :
      structuralRowEvaluatorBits request.q
          (thresholdRowResidualAssignment request liveScale input)
          (structuralCanonicalThresholdFourfoldRow algorithm request
            liveScale
            (thresholdPrimeUnionDenominator algorithm request
              (fixedTargetDenominator accuracyExponent request.q))
            (thresholdListUnionDenominator algorithm request
              (fixedTargetDenominator accuracyExponent request.q))
            sample residualOffset) ≤
        maximumBits)
    (hdata :
      runNPOracleProgram rowDataProgram maximumBits dataFuel
          (initialNPOracleState request.q handoff) =
        some
          (nativeInputRequest
            (finiteAssignmentContext
              (thresholdRowResidualAssignment request liveScale input))
            (encodedStructuralGF2
              (structuralCanonicalThresholdFourfoldRow algorithm request
                liveScale
                (thresholdPrimeUnionDenominator algorithm request
                  (fixedTargetDenominator accuracyExponent request.q))
                (thresholdListUnionDenominator algorithm request
                  (fixedTargetDenominator accuracyExponent request.q))
                sample residualOffset)))) :
    runNPOracleProgram (structuralRowEvaluatorProgram rowDataProgram)
        maximumBits
        (structuralRowEvaluatorFuel dataFuel
          (thresholdRowResidualAssignment request liveScale input)
          (structuralCanonicalThresholdFourfoldRow algorithm request
            liveScale
            (thresholdPrimeUnionDenominator algorithm request
              (fixedTargetDenominator accuracyExponent request.q))
            (thresholdListUnionDenominator algorithm request
              (fixedTargetDenominator accuracyExponent request.q))
            sample residualOffset))
        (initialNPOracleState request.q handoff) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (thresholdFourfoldRowRequest request rowIndex input))) := by
  have hdispatch :
      evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
          (thresholdFourfoldRowRequest request rowIndex input) =
        evaluateCanonicalThresholdFourfoldRow algorithm request liveScale
          (fixedTargetDenominator accuracyExponent request.q) rowIndex
          (encodeBitInput input) :=
    evaluateCanonicalFourfoldRow_threshold algorithm liveScale
      accuracyExponent request rowIndex input
  have hseed :
      evaluateCanonicalThresholdFourfoldRow algorithm request liveScale
          (fixedTargetDenominator accuracyExponent request.q) rowIndex
          (encodeBitInput input) =
        executableCanonicalThresholdFourfoldRow algorithm request liveScale
          (thresholdPrimeUnionDenominator algorithm request
            (fixedTargetDenominator accuracyExponent request.q))
          (thresholdListUnionDenominator algorithm request
            (fixedTargetDenominator accuracyExponent request.q))
          input sample := by
    unfold evaluateCanonicalThresholdFourfoldRow
    dsimp only
    rw [hsample, rowBitInputOfCode_encode]
  have hrow :
      evaluateStructuralGF2
          (encodedFiniteBooleanAssignment
            (thresholdRowResidualAssignment request liveScale input))
          (structuralCanonicalThresholdFourfoldRow algorithm request
            liveScale
            (thresholdPrimeUnionDenominator algorithm request
              (fixedTargetDenominator accuracyExponent request.q))
            (thresholdListUnionDenominator algorithm request
              (fixedTargetDenominator accuracyExponent request.q))
            sample residualOffset) =
        executableCanonicalThresholdFourfoldRow algorithm request liveScale
          (thresholdPrimeUnionDenominator algorithm request
            (fixedTargetDenominator accuracyExponent request.q))
          (thresholdListUnionDenominator algorithm request
            (fixedTargetDenominator accuracyExponent request.q))
          input sample :=
    evaluateStructuralCanonicalThresholdFourfoldRow algorithm request
      liveScale
      (thresholdPrimeUnionDenominator algorithm request
        (fixedTargetDenominator accuracyExponent request.q))
      (thresholdListUnionDenominator algorithm request
        (fixedTargetDenominator accuracyExponent request.q))
      input sample residualOffset hoffset
  rw [hdispatch, hseed, ← hrow]
  exact run_structuralRowEvaluatorProgram rowDataProgram
    (thresholdRowResidualAssignment request liveScale input)
    (structuralCanonicalThresholdFourfoldRow algorithm request liveScale
      (thresholdPrimeUnionDenominator algorithm request
        (fixedTargetDenominator accuracyExponent request.q))
      (thresholdListUnionDenominator algorithm request
        (fixedTargetDenominator accuracyExponent request.q))
      sample residualOffset)
    maximumBits request.q handoff dataFuel hbits hdata

theorem run_structuralForkRowEvaluatorProgram_threshold
    (tableProgram polynomialProgram : NPOracleProgram)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q)
    (sample :
      PrimeIndex
          (thresholdPrimeCutoff algorithm request
            (thresholdPrimeUnionDenominator algorithm request
              (fixedTargetDenominator accuracyExponent request.q))) ×
        NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences request)
          liveScale
          (thresholdListUnionDenominator algorithm request
            (fixedTargetDenominator accuracyExponent request.q)))
    (hsample :
      decodePrimeListSample
          (cutoff :=
            thresholdPrimeCutoff algorithm request
              (thresholdPrimeUnionDenominator algorithm request
                (fixedTargetDenominator accuracyExponent request.q)))
          (thresholdFourfoldOccurrences request) liveScale
          (thresholdListUnionDenominator algorithm request
            (fixedTargetDenominator accuracyExponent request.q)) rowIndex =
        some sample)
    (residualOffset : ThresholdChildSelection algorithm request → ℕ)
    (hoffset : ∀ selection,
      residualOffset selection =
        modularResidualOffset (thresholdFourfoldOccurrences request)
          liveScale input
          (thresholdSelectionEquation algorithm request selection)
          sample.1.val)
    (maximumBits handoff tableBits polynomialBits tableFuel
      polynomialFuel : ℕ)
    (hbits :
      structuralForkRowEvaluatorBits request.q handoff tableBits
          polynomialBits
          (thresholdRowResidualAssignment request liveScale input)
          (structuralCanonicalThresholdFourfoldRow algorithm request
            liveScale
            (thresholdPrimeUnionDenominator algorithm request
              (fixedTargetDenominator accuracyExponent request.q))
            (thresholdListUnionDenominator algorithm request
              (fixedTargetDenominator accuracyExponent request.q))
            sample residualOffset) ≤
        maximumBits)
    (htable :
      runNPOracleProgram tableProgram tableBits tableFuel
          (initialNPOracleState request.q handoff) =
        some
          (finiteAssignmentContext
            (thresholdRowResidualAssignment request liveScale input)))
    (hpolynomial :
      runNPOracleProgram polynomialProgram polynomialBits polynomialFuel
          (initialNPOracleState request.q handoff) =
        some
          (encodedStructuralGF2
            (structuralCanonicalThresholdFourfoldRow algorithm request
              liveScale
              (thresholdPrimeUnionDenominator algorithm request
                (fixedTargetDenominator accuracyExponent request.q))
              (thresholdListUnionDenominator algorithm request
                (fixedTargetDenominator accuracyExponent request.q))
              sample residualOffset))) :
    runNPOracleProgram
        (structuralForkRowEvaluatorProgram tableProgram polynomialProgram)
        maximumBits
        (structuralForkRowEvaluatorFuel tableProgram polynomialProgram
          tableFuel polynomialFuel
          (thresholdRowResidualAssignment request liveScale input)
          (structuralCanonicalThresholdFourfoldRow algorithm request
            liveScale
            (thresholdPrimeUnionDenominator algorithm request
              (fixedTargetDenominator accuracyExponent request.q))
            (thresholdListUnionDenominator algorithm request
              (fixedTargetDenominator accuracyExponent request.q))
            sample residualOffset))
        (initialNPOracleState request.q handoff) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (thresholdFourfoldRowRequest request rowIndex input))) := by
  have hunfold :
      structuralForkRowEvaluatorBits request.q handoff tableBits
          polynomialBits
          (thresholdRowResidualAssignment request liveScale input)
          (structuralCanonicalThresholdFourfoldRow algorithm request
            liveScale
            (thresholdPrimeUnionDenominator algorithm request
              (fixedTargetDenominator accuracyExponent request.q))
            (thresholdListUnionDenominator algorithm request
              (fixedTargetDenominator accuracyExponent request.q))
            sample residualOffset) =
        max
          (structuralRowEvaluatorBits request.q
            (thresholdRowResidualAssignment request liveScale input)
            (structuralCanonicalThresholdFourfoldRow algorithm request
              liveScale
              (thresholdPrimeUnionDenominator algorithm request
                (fixedTargetDenominator accuracyExponent request.q))
              (thresholdListUnionDenominator algorithm request
                (fixedTargetDenominator accuracyExponent request.q))
              sample residualOffset))
          (structuralRowDataBits request.q handoff tableBits polynomialBits
            (thresholdRowResidualAssignment request liveScale input)
            (structuralCanonicalThresholdFourfoldRow algorithm request
              liveScale
              (thresholdPrimeUnionDenominator algorithm request
                (fixedTargetDenominator accuracyExponent request.q))
              (thresholdListUnionDenominator algorithm request
                (fixedTargetDenominator accuracyExponent request.q))
              sample residualOffset)) :=
    rfl
  rw [hunfold] at hbits
  have hevaluatorBits :
      structuralRowEvaluatorBits request.q
          (thresholdRowResidualAssignment request liveScale input)
          (structuralCanonicalThresholdFourfoldRow algorithm request
            liveScale
            (thresholdPrimeUnionDenominator algorithm request
              (fixedTargetDenominator accuracyExponent request.q))
            (thresholdListUnionDenominator algorithm request
              (fixedTargetDenominator accuracyExponent request.q))
            sample residualOffset) ≤
        maximumBits := by
    omega
  have hdataBits :
      structuralRowDataBits request.q handoff tableBits polynomialBits
          (thresholdRowResidualAssignment request liveScale input)
          (structuralCanonicalThresholdFourfoldRow algorithm request
            liveScale
            (thresholdPrimeUnionDenominator algorithm request
              (fixedTargetDenominator accuracyExponent request.q))
            (thresholdListUnionDenominator algorithm request
              (fixedTargetDenominator accuracyExponent request.q))
            sample residualOffset) ≤
        maximumBits := by
    omega
  exact run_structuralRowEvaluatorProgram_thresholdFourfoldRow
    (structuralRowDataProgram tableProgram polynomialProgram) algorithm
    request liveScale accuracyExponent rowIndex input sample hsample
    residualOffset hoffset maximumBits handoff
    (structuralRowDataFuel tableProgram polynomialProgram tableFuel
      polynomialFuel)
    hevaluatorBits
    (run_bits_mono
      (run_structuralRowDataProgram tableProgram polynomialProgram
        (thresholdRowResidualAssignment request liveScale input)
        (structuralCanonicalThresholdFourfoldRow algorithm request liveScale
          (thresholdPrimeUnionDenominator algorithm request
            (fixedTargetDenominator accuracyExponent request.q))
          (thresholdListUnionDenominator algorithm request
            (fixedTargetDenominator accuracyExponent request.q))
          sample residualOffset)
        request.q handoff tableBits polynomialBits tableFuel polynomialFuel
        htable hpolynomial)
      hdataBits)

/-! ## §15 Malformed row indices

Row indices outside the finite seed space evaluate to `false` rather than
wrapping.  The evaluator reproduces that convention exactly: the producer
emits the zero polynomial and the machine's parity fold is empty, so no
partiality or truncation is introduced at the boundary. -/

theorem run_structuralRowEvaluatorProgram_symmetricFourfoldRow_none
    (rowDataProgram : NPOracleProgram)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q)
    (hsample :
      decodeNormalizedOccurrenceListSeed
          (symmetricFourfoldOccurrences request) liveScale
          (symmetricListDenominator request
            (fixedTargetDenominator accuracyExponent request.q)) rowIndex =
        none)
    (maximumBits handoff dataFuel : ℕ)
    (hbits :
      structuralRowEvaluatorBits request.q
          (symmetricRowResidualAssignment request liveScale input)
          structuralGF2Zero ≤
        maximumBits)
    (hdata :
      runNPOracleProgram rowDataProgram maximumBits dataFuel
          (initialNPOracleState request.q handoff) =
        some
          (nativeInputRequest
            (finiteAssignmentContext
              (symmetricRowResidualAssignment request liveScale input))
            (encodedStructuralGF2 structuralGF2Zero))) :
    runNPOracleProgram (structuralRowEvaluatorProgram rowDataProgram)
        maximumBits
        (structuralRowEvaluatorFuel dataFuel
          (symmetricRowResidualAssignment request liveScale input)
          structuralGF2Zero)
        (initialNPOracleState request.q handoff) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (symmetricFourfoldRowRequest request rowIndex input))) := by
  have hvalue :
      evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
          (symmetricFourfoldRowRequest request rowIndex input) =
        evaluateStructuralGF2
          (encodedFiniteBooleanAssignment
            (symmetricRowResidualAssignment request liveScale input))
          structuralGF2Zero := by
    rw [evaluateCanonicalFourfoldRow_symmetric algorithm liveScale
      accuracyExponent request rowIndex input, evaluateStructuralGF2_zero]
    unfold evaluateCanonicalSymmetricFourfoldRow
    dsimp only
    rw [hsample]
  rw [hvalue]
  exact run_structuralRowEvaluatorProgram rowDataProgram
    (symmetricRowResidualAssignment request liveScale input)
    structuralGF2Zero maximumBits request.q handoff dataFuel hbits hdata

theorem run_structuralRowEvaluatorProgram_thresholdFourfoldRow_none
    (rowDataProgram : NPOracleProgram)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q)
    (hsample :
      decodePrimeListSample
          (cutoff :=
            thresholdPrimeCutoff algorithm request
              (thresholdPrimeUnionDenominator algorithm request
                (fixedTargetDenominator accuracyExponent request.q)))
          (thresholdFourfoldOccurrences request) liveScale
          (thresholdListUnionDenominator algorithm request
            (fixedTargetDenominator accuracyExponent request.q)) rowIndex =
        none)
    (maximumBits handoff dataFuel : ℕ)
    (hbits :
      structuralRowEvaluatorBits request.q
          (thresholdRowResidualAssignment request liveScale input)
          structuralGF2Zero ≤
        maximumBits)
    (hdata :
      runNPOracleProgram rowDataProgram maximumBits dataFuel
          (initialNPOracleState request.q handoff) =
        some
          (nativeInputRequest
            (finiteAssignmentContext
              (thresholdRowResidualAssignment request liveScale input))
            (encodedStructuralGF2 structuralGF2Zero))) :
    runNPOracleProgram (structuralRowEvaluatorProgram rowDataProgram)
        maximumBits
        (structuralRowEvaluatorFuel dataFuel
          (thresholdRowResidualAssignment request liveScale input)
          structuralGF2Zero)
        (initialNPOracleState request.q handoff) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (thresholdFourfoldRowRequest request rowIndex input))) := by
  have hvalue :
      evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
          (thresholdFourfoldRowRequest request rowIndex input) =
        evaluateStructuralGF2
          (encodedFiniteBooleanAssignment
            (thresholdRowResidualAssignment request liveScale input))
          structuralGF2Zero := by
    rw [evaluateCanonicalFourfoldRow_threshold algorithm liveScale
      accuracyExponent request rowIndex input, evaluateStructuralGF2_zero]
    unfold evaluateCanonicalThresholdFourfoldRow
    dsimp only
    rw [hsample]
  rw [hvalue]
  exact run_structuralRowEvaluatorProgram rowDataProgram
    (thresholdRowResidualAssignment request liveScale input)
    structuralGF2Zero maximumBits request.q handoff dataFuel hbits hdata

end NearCubicWires.CanonicalStructuralGF2EvaluationProgram
