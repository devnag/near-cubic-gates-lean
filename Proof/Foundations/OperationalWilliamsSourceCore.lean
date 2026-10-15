import Proof.Foundations.LocalBitMultitapeCore
import StatementSupport

/-!
# Cycle-free operational published source core

This lower layer contains exactly the finite local bit-machine semantics,
streamed Williams carrier, literal-receipt local Williams certificate,
canonical rule-table description, and faithful public contract needed by
`SourceContracts`.  It imports no supplier, recovery, or source-contract
consumer.  The semantic-only constructor from an arbitrary rectangular
algorithm intentionally remains in the higher diagnostic module.
-/

namespace NearCubicWires.WilliamsProductCertificate

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces

@[simp] theorem rowMajorNatMatrix_length {rows columns : ℕ}
    (matrix : NatMatrix rows columns) :
    (rowMajorNatMatrix matrix).length = rows * columns := by
  simp [rowMajorNatMatrix, List.length_flatten, List.sum_ofFn]

/-- One shared fast computation together with its sequential output view and
total bit-operation charge. -/
structure StreamedRectangularProductRun
    (request : RectangularProductRequest) where
  output : NatMatrix request.dimension request.dimension
  emittedCells : List ℕ
  bitSteps : ℕ
  emittedCellBits : ℕ
  emitsRowMajor : emittedCells = rowMajorNatMatrix output

/-- Source-faithful streamed carrier.  `bitSteps` charges the shared run once;
there is no per-cell invocation of the fast algorithm. -/
structure StreamedRectangularProductCertificate where
  run : (request : RectangularProductRequest) →
    StreamedRectangularProductRun request
  onset : ℕ
  coefficient : ℕ
  logExponent : ℕ
  coefficientPositive : 0 < coefficient
  correct : ∀ request, onset ≤ request.dimension →
    (run request).output =
      integerMatrixProduct request.left request.right
  cellBits : ∀ request, onset ≤ request.dimension →
    ∀ value ∈ (run request).emittedCells,
      natBitLength value ≤ (run request).emittedCellBits
  polylogCells : ∀ request, onset ≤ request.dimension →
    (run request).emittedCellBits ≤ natBitLength request.dimension
  totalBitCost : ∀ request, onset ≤ request.dimension →
    (run request).bitSteps ≤
      coefficient * request.dimension ^ 2 *
        logScale request.dimension ^ logExponent

/-- The source-facing proposition proposed as the corrected published field. -/
def StreamedBooleanRectangularProductContract : Prop :=
  Nonempty StreamedRectangularProductCertificate

/-- The ordinary semantic algorithm recovered from the streamed run. -/
def StreamedRectangularProductCertificate.toSemantic
    (certificate : StreamedRectangularProductCertificate) :
    RectangularProductAlgorithm where
  compute := fun U left right =>
    (certificate.run ⟨U, left, right⟩).output
  steps := fun U left right =>
    (certificate.run ⟨U, left, right⟩).bitSteps

theorem streamedRectangularProduct_implies_semantic
    (certificate : StreamedRectangularProductCertificate) :
    BooleanRectangularProductContract := by
  refine ⟨certificate.toSemantic, certificate.onset,
    certificate.coefficient, certificate.logExponent,
    certificate.coefficientPositive, ?_⟩
  intro U hU left right
  exact ⟨certificate.correct ⟨U, left, right⟩ hU,
    certificate.totalBitCost ⟨U, left, right⟩ hU⟩

end NearCubicWires.WilliamsProductCertificate

namespace NearCubicWires.WilliamsLoaderForms

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.LocalBitMultitape
open NearCubicWires.SourceInterfaces
open NearCubicWires.WilliamsProductCertificate

/-! ## 1. Canonical explicit-tape Williams source carrier -/

/-- A source-faithful operational carrier for Williams's explicit-input
multitape statement.  The transition count comes from `LocalBitMultitape.run`,
not from a user-provided cost attached to a whole-configuration update. -/
structure WilliamsLocalBitTMRectangularProductCertificate where
  streamed : StreamedRectangularProductCertificate
  tapeCount : ℕ
  stateCount : ℕ
  machine : Machine tapeCount stateCount
  leftInputTape : Fin tapeCount
  rightInputTape : Fin tapeCount
  outputTape : Fin tapeCount
  left_ne_right : leftInputTape ≠ rightInputTape
  inputTapes : RectangularProductRequest → Fin tapeCount → List Bool
  leftInput_eq : ∀ request,
    inputTapes request leftInputTape = rowMajorBitMatrix request.left
  rightInput_eq : ∀ request,
    inputTapes request rightInputTape = rowMajorBitMatrix request.right
  otherInputBlank : ∀ request tape,
    tape ≠ leftInputTape → tape ≠ rightInputTape →
      inputTapes request tape = []
  fuel : RectangularProductRequest → ℕ
  receipt : RectangularProductRequest → ExecutionReceipt tapeCount stateCount
  runs : ∀ request,
    run machine (fuel request) (inputTapes request) = some (receipt request)
  finalHalted : ∀ request,
    machine.halted (receipt request).final.control = true
  outputTape_eq : ∀ request,
    (receipt request).final.tapes outputTape =
      encodedNatCellTape (natBitLength request.dimension)
        (streamed.run request).emittedCells
  machineSteps_eq : ∀ request,
    (receipt request).steps = (streamed.run request).bitSteps

theorem WilliamsLocalBitTMRectangularProductCertificate.steps_le
    (source : WilliamsLocalBitTMRectangularProductCertificate)
    (request : RectangularProductRequest)
    (hrequest : source.streamed.onset ≤ request.dimension) :
    (source.receipt request).steps ≤
      source.streamed.coefficient * request.dimension ^ 2 *
        logScale request.dimension ^ source.streamed.logExponent := by
  rw [source.machineSteps_eq request]
  exact source.streamed.totalBitCost request hrequest

end NearCubicWires.WilliamsLoaderForms

namespace NearCubicWires.WilliamsPublishedForm

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.LocalBitMultitape
open NearCubicWires.SourceInterfaces
open NearCubicWires.WilliamsProductCertificate
open NearCubicWires.WilliamsLoaderForms

/-! ## Canonical encoding of the exhibited finite rule table -/

def encodeHeadMove : HeadMove → ℕ
  | .left => 0
  | .stay => 1
  | .right => 2

def encodeOptionalWrite : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

def encodeAction {tapeCount stateCount : ℕ}
    (action : Action tapeCount stateCount) : List ℕ :=
  [action.nextControl.val] ++
    List.ofFn (fun tape : Fin tapeCount =>
      encodeOptionalWrite (action.write tape)) ++
    List.ofFn (fun tape : Fin tapeCount =>
      encodeHeadMove (action.move tape))

def encodeRuleOutput {tapeCount stateCount : ℕ} :
    Option (Action tapeCount stateCount) → List ℕ
  | none => [0]
  | some action => 1 :: encodeAction action

/-- The `code`-th scanned-symbol vector.  The canonical table below enumerates
all `2^tapeCount` vectors for every finite control state. -/
def scannedVector (tapeCount code : ℕ) : Fin tapeCount → Bool :=
  fun tape => code.testBit tape.val

theorem encodeScannedVector_lt_pow {tapeCount : ℕ}
    (scanned : Fin tapeCount → Bool) :
    encodeBitInput scanned < 2 ^ tapeCount := by
  induction tapeCount with
  | zero =>
      simp [encodeBitInput]
  | succ tapeCount inductionHypothesis =>
      rw [encodeBitInput, Fin.sum_univ_succ]
      have htail :=
        inductionHypothesis (fun tape : Fin tapeCount => scanned tape.succ)
      unfold encodeBitInput at htail
      have htail' :
          (∑ tape : Fin tapeCount,
              if scanned tape.succ then 2 ^ tape.val else 0) <
            2 ^ tapeCount := by
        simpa using htail
      have hshift :
          (∑ tape : Fin tapeCount,
              if scanned tape.succ then 2 ^ tape.succ.val else 0) =
            2 * ∑ tape : Fin tapeCount,
              if scanned tape.succ then 2 ^ tape.val else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro tape _htape
        simp only [Fin.val_succ]
        split <;> simp_all [pow_succ, Nat.mul_comm]
      rw [hshift]
      simp only [Fin.val_zero, pow_zero]
      rw [pow_succ]
      split <;> omega

def scannedCode {tapeCount : ℕ}
    (scanned : Fin tapeCount → Bool) : Fin (2 ^ tapeCount) :=
  ⟨encodeBitInput scanned, encodeScannedVector_lt_pow scanned⟩

/-- The table enumeration is complete: every possible scanned-symbol function
occurs at its binary code. -/
@[simp] theorem scannedVector_scannedCode {tapeCount : ℕ}
    (scanned : Fin tapeCount → Bool) :
    scannedVector tapeCount (scannedCode scanned).val = scanned := by
  funext tape
  simp only [scannedVector, scannedCode]
  rw [encodeBitInput_eq_ofBits,
    Nat.testBit_ofBits_lt _ _ tape.isLt]

def canonicalRuleTableFields {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount) : List ℕ :=
  (List.ofFn fun state : Fin stateCount =>
    (List.ofFn fun code : Fin (2 ^ tapeCount) =>
      encodeRuleOutput
        (machine.rule state (scannedVector tapeCount code.val))).flatten).flatten

def canonicalMachineFields {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount) : List ℕ :=
  [tapeCount, stateCount, machine.start.val] ++
    List.ofFn (fun state : Fin stateCount =>
      (machine.halted state).toNat) ++
    canonicalRuleTableFields machine

/-- A description computed from the actual start state, halt predicate, and
every entry of the finite rule table.  It never reads
`Machine.descriptionBits`. -/
def canonicalMachineDescription {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount) : List Bool :=
  (canonicalMachineFields machine).flatMap framedNatBits

def canonicalMachineDescriptionBits {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount) : ℕ :=
  (canonicalMachineDescription machine).length

@[simp] theorem canonicalMachineDescriptionBits_eq_length
    {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount) :
    canonicalMachineDescriptionBits machine =
      (canonicalMachineDescription machine).length :=
  rfl

/-! ## Corrected source field -/

/-- The source object stored by the corrected rectangular-product field.

`certificate` fixes the machine, tape ABI, onset, and all asymptotic constants
before quantifying over requests.  `descriptionBits_eq` prevents the legacy
author-supplied description field from lying about that exhibited rule table.
-/
structure FaithfulWilliamsRectangularProductSource where
  certificate : WilliamsLocalBitTMRectangularProductCertificate
  descriptionBits_eq :
    certificate.machine.descriptionBits =
      canonicalMachineDescriptionBits certificate.machine

/-- Proposed replacement type for
`PublishedContracts.booleanRectangularProduct`. -/
def FaithfulWilliamsRectangularProductContract : Prop :=
  Nonempty FaithfulWilliamsRectangularProductSource

noncomputable def selectedSource
    (contract : FaithfulWilliamsRectangularProductContract) :
    FaithfulWilliamsRectangularProductSource :=
  Classical.choice contract

noncomputable def selectedLocalCertificate
    (contract : FaithfulWilliamsRectangularProductContract) :
    WilliamsLocalBitTMRectangularProductCertificate :=
  (selectedSource contract).certificate

theorem selectedLocalCertificate_descriptionBits_eq
    (contract : FaithfulWilliamsRectangularProductContract) :
    (selectedLocalCertificate contract).machine.descriptionBits =
      canonicalMachineDescriptionBits
        (selectedLocalCertificate contract).machine :=
  (selectedSource contract).descriptionBits_eq

/-! ## Safe projections -/

def FaithfulWilliamsRectangularProductSource.toStreamed
    (source : FaithfulWilliamsRectangularProductSource) :
    StreamedRectangularProductCertificate :=
  source.certificate.streamed

def FaithfulWilliamsRectangularProductSource.toSemantic
    (source : FaithfulWilliamsRectangularProductSource) :
    RectangularProductAlgorithm :=
  source.toStreamed.toSemantic

theorem faithfulWilliams_implies_streamed :
    FaithfulWilliamsRectangularProductContract →
      StreamedBooleanRectangularProductContract := by
  rintro ⟨source⟩
  exact ⟨source.toStreamed⟩

theorem faithfulWilliams_implies_semantic :
    FaithfulWilliamsRectangularProductContract →
      BooleanRectangularProductContract := by
  rintro ⟨source⟩
  exact streamedRectangularProduct_implies_semantic source.toStreamed

/-! ## Literal-receipt consequences used by downstream consumers -/

theorem selectedLocalCertificate_runs
    (contract : FaithfulWilliamsRectangularProductContract)
    (request : RectangularProductRequest) :
    run (selectedLocalCertificate contract).machine
        ((selectedLocalCertificate contract).fuel request)
        ((selectedLocalCertificate contract).inputTapes request) =
      some ((selectedLocalCertificate contract).receipt request) :=
  (selectedLocalCertificate contract).runs request

theorem selectedLocalCertificate_otherInputBlank
    (contract : FaithfulWilliamsRectangularProductContract)
    (request : RectangularProductRequest)
    (tape : Fin (selectedLocalCertificate contract).tapeCount)
    (hleft : tape ≠ (selectedLocalCertificate contract).leftInputTape)
    (hright : tape ≠ (selectedLocalCertificate contract).rightInputTape) :
    (selectedLocalCertificate contract).inputTapes request tape = [] :=
  (selectedLocalCertificate contract).otherInputBlank request tape hleft hright

theorem selectedLocalCertificate_steps_eq_streamed
    (contract : FaithfulWilliamsRectangularProductContract)
    (request : RectangularProductRequest) :
    ((selectedLocalCertificate contract).receipt request).steps =
      ((selectedLocalCertificate contract).streamed.run request).bitSteps :=
  (selectedLocalCertificate contract).machineSteps_eq request

theorem selectedLocalCertificate_steps_le
    (contract : FaithfulWilliamsRectangularProductContract)
    (request : RectangularProductRequest)
    (hrequest :
      (selectedLocalCertificate contract).streamed.onset ≤ request.dimension) :
    ((selectedLocalCertificate contract).receipt request).steps ≤
      (selectedLocalCertificate contract).streamed.coefficient *
        request.dimension ^ 2 *
        logScale request.dimension ^
          (selectedLocalCertificate contract).streamed.logExponent :=
  (selectedLocalCertificate contract).steps_le request hrequest

theorem selectedLocalCertificate_outputTape_eq
    (contract : FaithfulWilliamsRectangularProductContract)
    (request : RectangularProductRequest) :
    ((selectedLocalCertificate contract).receipt request).final.tapes
        (selectedLocalCertificate contract).outputTape =
      encodedNatCellTape (natBitLength request.dimension)
        ((selectedLocalCertificate contract).streamed.run request).emittedCells :=
  (selectedLocalCertificate contract).outputTape_eq request

end NearCubicWires.WilliamsPublishedForm
