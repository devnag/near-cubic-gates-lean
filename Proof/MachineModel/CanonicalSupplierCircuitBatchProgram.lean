import Proof.MachineModel.CanonicalAggregationEnvelopeProgram
import Proof.Circuits.CanonicalBalancedCall
import Proof.MachineModel.CanonicalSupplierCircuitHeaderProgram
import Proof.MachineModel.PreserveRightProgram

namespace NearCubicWires.CanonicalSupplierCircuitBatchProgram

open NearCubicWires
open NearCubicWires.CanonicalAggregationEnvelopeProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalSupplierCircuitHeaderProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## Retain the batch context once -/

def supplierCircuitBatchContext (mode q : ℕ) : ℕ :=
  Nat.pair mode q

def supplierCircuitBatchAdapterOutput
    (mode q circuitTree : ℕ) : ℕ :=
  Nat.pair circuitTree (supplierCircuitBatchContext mode q)

/-- Reframe `pair(mode, pair(q, tree))` as `pair(tree, pair(mode, q))`. -/
def supplierCircuitBatchAdapterProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 2 4 6 5
  , .pair 5 6 0 6
  , .halt 0
  ]

@[simp] theorem supplierCircuitBatchAdapterProgram_oracleFree :
    OracleFree supplierCircuitBatchAdapterProgram := by
  rfl

def supplierCircuitBatchAdapterBits
    (mode q circuitTree : ℕ) : ℕ :=
  max
    (natBitLength (aggregationEnvelopeContext mode q circuitTree))
    (natBitLength
      (supplierCircuitBatchAdapterOutput mode q circuitTree))

theorem run_supplierCircuitBatchAdapterProgram
    (mode q circuitTree : ℕ) :
    runNPOracleProgram supplierCircuitBatchAdapterProgram
        (supplierCircuitBatchAdapterBits mode q circuitTree)
        7
        (initialNPOracleState q
          (aggregationEnvelopeContext mode q circuitTree)) =
      some (supplierCircuitBatchAdapterOutput mode q circuitTree) := by
  let qTree := Nat.pair q circuitTree
  let context := supplierCircuitBatchContext mode q
  let input := aggregationEnvelopeContext mode q circuitTree
  let output := supplierCircuitBatchAdapterOutput mode q circuitTree
  have hinput :
      natBitLength input ≤
        supplierCircuitBatchAdapterBits mode q circuitTree :=
    Nat.le_max_left _ _
  have houtput :
      natBitLength output ≤
        supplierCircuitBatchAdapterBits mode q circuitTree :=
    Nat.le_max_right _ _
  have hmode :
      natBitLength mode ≤
        supplierCircuitBatchAdapterBits mode q circuitTree :=
    (natBitLength_mono (Nat.left_le_pair mode qTree)).trans hinput
  have hqTree :
      natBitLength qTree ≤
        supplierCircuitBatchAdapterBits mode q circuitTree :=
    (natBitLength_mono (Nat.right_le_pair mode qTree)).trans hinput
  have hq :
      natBitLength q ≤
        supplierCircuitBatchAdapterBits mode q circuitTree :=
    (natBitLength_mono (Nat.left_le_pair q circuitTree)).trans hqTree
  have htree :
      natBitLength circuitTree ≤
        supplierCircuitBatchAdapterBits mode q circuitTree :=
    (natBitLength_mono (Nat.right_le_pair q circuitTree)).trans hqTree
  have hcontext :
      natBitLength context ≤
        supplierCircuitBatchAdapterBits mode q circuitTree := by
    apply (natBitLength_mono ?_).trans houtput
    exact Nat.right_le_pair circuitTree context
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := mode)
    (by rfl) rfl
    (by simp [initialNPOracleState, aggregationEnvelopeContext])
    hmode]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := qTree)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, aggregationEnvelopeContext, qTree])
    hqTree]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := q)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, qTree])
    hq]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := circuitTree)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, qTree])
    htree]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := context)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, context,
        supplierCircuitBatchContext])
    hcontext]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, output,
        supplierCircuitBatchAdapterOutput, context])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output])
    houtput

/-! ## Shape-preserving constant-length call framing -/

def zeroLengthCircuitRequest (circuitCode : ℕ) : ℕ :=
  Nat.pair 0 circuitCode

def supplierCircuitRequestTreeProgram : NPOracleProgram :=
  balancedTraversalController 34 36 ++
    [ .set 4 0 35
    , .pair 4 3 3 balancedTraversalLeafReturnPc
    , .halt 0
    ]

@[simp] theorem supplierCircuitRequestTreeProgram_oracleFree :
    OracleFree supplierCircuitRequestTreeProgram := by
  rfl

theorem supplierCircuitRequestTreeProgram_controllerAt :
    BalancedTraversalControllerAt
      supplierCircuitRequestTreeProgram 34 36 := by
  intro pc instruction hlookup
  have hpc : pc < (balancedTraversalController 34 36).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [supplierCircuitRequestTreeProgram]
  rw [List.getElem?_append_left hpc]
  exact hlookup

def supplierCircuitRequestTreeFuel
    (circuitCodes : List ℕ) : ℕ :=
  balancedTraversalStructuralSteps
      (balancedTraversalTree circuitCodes) +
    2 * circuitCodes.length + 2

def supplierCircuitRequestTreeBits
    (circuitCodes : List ℕ) : ℕ :=
  balancedTraversalRequiredBits zeroLengthCircuitRequest
    (balancedTraversalTree circuitCodes) []

private theorem zeroLengthCircuitRequest_zero_bits
    (circuitCode maximumBits : ℕ)
    (houtput :
      natBitLength (zeroLengthCircuitRequest circuitCode) ≤
        maximumBits) :
    natBitLength 0 ≤ maximumBits := by
  apply (natBitLength_mono ?_).trans houtput
  exact Nat.left_le_pair 0 circuitCode

private theorem run_supplierCircuitRequestTreeLeaf
    (circuitCode maximumBits : ℕ) (entry : NPOracleState)
    (hpc : entry.pc = 34)
    (hcurrent : entry.registers 0 = Nat.pair 1 circuitCode)
    (hatom : entry.registers 3 = circuitCode)
    (hbits :
      natBitLength (zeroLengthCircuitRequest circuitCode) ≤
        maximumBits) :
    ∃ finish,
      RunsToIn supplierCircuitRequestTreeProgram maximumBits
          2 entry finish ∧
      finish.pc = balancedTraversalLeafReturnPc ∧
      finish.registers 0 = entry.registers 0 ∧
      finish.registers 2 = entry.registers 2 ∧
      finish.registers 3 =
        zeroLengthCircuitRequest circuitCode ∧
      SameTraversalContextFrom 9 entry finish := by
  let state1 := (entry.write 4 0).jump 35
  let finish :=
    (state1.write 3 (zeroLengthCircuitRequest circuitCode)).jump
      balancedTraversalLeafReturnPc
  have hzero :=
    zeroLengthCircuitRequest_zero_bits circuitCode maximumBits hbits
  have hruns :
      RunsToIn supplierCircuitRequestTreeProgram maximumBits
        2 entry finish := by
    intro extra
    rw [show 2 + extra = (1 + extra) + 1 by omega]
    rw [run_set_instruction (fuel := 1 + extra)
      (by rfl) hpc hzero]
    change
      runNPOracleProgram supplierCircuitRequestTreeProgram
          maximumBits (1 + extra) state1 =
        runNPOracleProgram supplierCircuitRequestTreeProgram
          maximumBits extra finish
    rw [show 1 + extra = extra + 1 by omega]
    rw [run_pair_instruction (fuel := extra)
      (value := zeroLengthCircuitRequest circuitCode)
      (by rfl) rfl
      (by
        simp [state1, hatom, zeroLengthCircuitRequest])
      hbits]
  refine ⟨finish, hruns, rfl, ?_, ?_, ?_, ?_⟩
  · simp [finish, state1, hcurrent, NPOracleState.write,
      NPOracleState.jump]
  · simp [finish, state1, NPOracleState.write,
      NPOracleState.jump]
  · simp [finish]
  · constructor
    · simp [finish, state1, NPOracleState.write,
        NPOracleState.jump]
    · intro register hregister
      have hthree : register ≠ 3 := by omega
      have hfour : register ≠ 4 := by omega
      simp [finish, state1, NPOracleState.write,
        NPOracleState.jump, hthree, hfour]

theorem run_supplierCircuitRequestTreeProgram
    (inputLength : ℕ) (circuitCodes : List ℕ) :
    runNPOracleProgram supplierCircuitRequestTreeProgram
        (supplierCircuitRequestTreeBits circuitCodes)
        (supplierCircuitRequestTreeFuel circuitCodes)
        (initialNPOracleState inputLength
          (encodeBalancedList circuitCodes)) =
      some
        (encodeBalancedList
          (circuitCodes.map zeroLengthCircuitRequest)) := by
  let initial :=
    initialNPOracleState inputLength
      (encodeBalancedList circuitCodes)
  have hfit :
      BalancedTraversalFits
        (supplierCircuitRequestTreeBits circuitCodes)
        zeroLengthCircuitRequest
        (balancedTraversalTree circuitCodes) [] :=
    (balancedTraversalRequiredBits_le_iff
      (supplierCircuitRequestTreeBits circuitCodes)
      zeroLengthCircuitRequest
      (balancedTraversalTree circuitCodes) []).mp (le_refl _)
  obtain ⟨finish, hruns, hpc, houtput, _hstack, _hpersistent⟩ :=
    run_balancedTraversal zeroLengthCircuitRequest (fun _ => 2)
      circuitCodes initial inputLength 9 (by omega)
      supplierCircuitRequestTreeProgram_controllerAt
      (by rfl)
      (by simp [initial, initialNPOracleState])
      (by simp [initial, initialNPOracleState])
      (by simp [initial, initialNPOracleState])
      hfit
      (by
        intro circuitCode _hcode entry hentryPc hcurrent
          hatom hbits _hentryLength
        exact run_supplierCircuitRequestTreeLeaf circuitCode
          (supplierCircuitRequestTreeBits circuitCodes) entry
          hentryPc hcurrent hatom hbits)
  have houtputBits :
      natBitLength
          (encodeBalancedList
            (circuitCodes.map zeroLengthCircuitRequest)) ≤
        supplierCircuitRequestTreeBits circuitCodes := by
    simpa [balancedTraversalTree_map_code] using hfit.output
  have hhalt :
      runNPOracleProgram supplierCircuitRequestTreeProgram
          (supplierCircuitRequestTreeBits circuitCodes) 1 finish =
        some
          (encodeBalancedList
            (circuitCodes.map zeroLengthCircuitRequest)) :=
    run_halt_instruction (fuel := 0) (by rfl) hpc houtput
      houtputBits
  rw [show supplierCircuitRequestTreeFuel circuitCodes =
      (balancedTraversalStructuralSteps
          (balancedTraversalTree circuitCodes) +
        (circuitCodes.map fun _ => 2).sum + 1) + 1 by
    simp [supplierCircuitRequestTreeFuel]
    omega]
  rw [hruns]
  exact hhalt

/-! ## One raw-header proof view and balanced call -/

/-- Proof-only view of the four canonical circuit fields.  The VM receives
only `code`; this structure is used to state exact executions without a
semantic circuit callback. -/
structure SupplierCircuitHeaderView where
  familyCode : ℕ
  bottomCount : ℕ
  bottomTree : ℕ
  topCode : ℕ
  deriving DecidableEq, Repr

def SupplierCircuitHeaderView.code
    (view : SupplierCircuitHeaderView) : ℕ :=
  supplierCircuitHeaderParserInput view.familyCode
    (encodeNat view.bottomCount) view.bottomTree view.topCode

def SupplierCircuitHeaderView.request
    (view : SupplierCircuitHeaderView) : ℕ :=
  zeroLengthCircuitRequest view.code

def SupplierCircuitHeaderView.output
    (view : SupplierCircuitHeaderView) : ℕ :=
  supplierCircuitHeaderOutput view.familyCode view.bottomCount
    view.bottomTree view.topCode

/-- Total proof-level projection of the fixed wire fields.  Production
execution is the parser theorem above; this definition only generates the
callee fuel/width certificate from the public code. -/
def decodeSupplierCircuitHeaderView
    (circuitCode : ℕ) : SupplierCircuitHeaderView :=
  let payload₀ := (Nat.unpair circuitCode).2
  let familyCode := (Nat.unpair payload₀).1
  let rest₁ := (Nat.unpair payload₀).2
  let payload₁ := (Nat.unpair rest₁).2
  let countCode := (Nat.unpair payload₁).1
  let rest₂ := (Nat.unpair payload₁).2
  let payload₂ := (Nat.unpair rest₂).2
  let bottomTree := (Nat.unpair payload₂).1
  let rest₃ := (Nat.unpair payload₂).2
  let payload₃ := (Nat.unpair rest₃).2
  let topCode := (Nat.unpair payload₃).1
  { familyCode
    bottomCount := (decodeNat countCode).getD 0
    bottomTree
    topCode }

@[simp] theorem decodeSupplierCircuitHeaderView_code
    (view : SupplierCircuitHeaderView) :
    decodeSupplierCircuitHeaderView view.code = view := by
  cases view
  simp [decodeSupplierCircuitHeaderView,
    SupplierCircuitHeaderView.code,
    supplierCircuitHeaderParserInput, encodeTaggedList]

def supplierCircuitHeaderRequestView
    (request : ℕ) : SupplierCircuitHeaderView :=
  decodeSupplierCircuitHeaderView (Nat.unpair request).2

def supplierCircuitHeaderRequestOutput (request : ℕ) : ℕ :=
  (supplierCircuitHeaderRequestView request).output

def supplierCircuitHeaderRequestFuel (request : ℕ) : ℕ :=
  supplierCircuitHeaderFuel
    (supplierCircuitHeaderRequestView request).bottomCount

def supplierCircuitHeaderRequestBits (request : ℕ) : ℕ :=
  let view := supplierCircuitHeaderRequestView request
  supplierCircuitHeaderBits 0 view.familyCode view.bottomCount
    view.bottomTree view.topCode

@[simp] theorem supplierCircuitHeaderRequestView_request
    (view : SupplierCircuitHeaderView) :
    supplierCircuitHeaderRequestView view.request = view := by
  simp [supplierCircuitHeaderRequestView,
    SupplierCircuitHeaderView.request, zeroLengthCircuitRequest]

@[simp] theorem supplierCircuitHeaderRequestOutput_request
    (view : SupplierCircuitHeaderView) :
    supplierCircuitHeaderRequestOutput view.request = view.output := by
  simp [supplierCircuitHeaderRequestOutput]

@[simp] theorem supplierCircuitHeaderRequestFuel_request
    (view : SupplierCircuitHeaderView) :
    supplierCircuitHeaderRequestFuel view.request =
      supplierCircuitHeaderFuel view.bottomCount := by
  simp [supplierCircuitHeaderRequestFuel]

@[simp] theorem supplierCircuitHeaderRequestBits_request
    (view : SupplierCircuitHeaderView) :
    supplierCircuitHeaderRequestBits view.request =
      supplierCircuitHeaderBits 0 view.familyCode view.bottomCount
        view.bottomTree view.topCode := by
  simp [supplierCircuitHeaderRequestBits]

@[simp] theorem supplierCircuitHeaderRequestView_zeroCode
    (view : SupplierCircuitHeaderView) :
    supplierCircuitHeaderRequestView
        (zeroLengthCircuitRequest view.code) = view := by
  simpa only [SupplierCircuitHeaderView.request] using
    supplierCircuitHeaderRequestView_request view

@[simp] theorem supplierCircuitHeaderRequestOutput_zeroCode
    (view : SupplierCircuitHeaderView) :
    supplierCircuitHeaderRequestOutput
        (zeroLengthCircuitRequest view.code) = view.output := by
  simp [supplierCircuitHeaderRequestOutput]

@[simp] theorem supplierCircuitHeaderRequestFuel_zeroCode
    (view : SupplierCircuitHeaderView) :
    supplierCircuitHeaderRequestFuel
        (zeroLengthCircuitRequest view.code) =
      supplierCircuitHeaderFuel view.bottomCount := by
  simp [supplierCircuitHeaderRequestFuel]

@[simp] theorem supplierCircuitHeaderRequestBits_zeroCode
    (view : SupplierCircuitHeaderView) :
    supplierCircuitHeaderRequestBits
        (zeroLengthCircuitRequest view.code) =
      supplierCircuitHeaderBits 0 view.familyCode view.bottomCount
        view.bottomTree view.topCode := by
  simp [supplierCircuitHeaderRequestBits]

def supplierCircuitHeaderRequests
    (views : List SupplierCircuitHeaderView) : List ℕ :=
  (views.map SupplierCircuitHeaderView.code).map
    zeroLengthCircuitRequest

def supplierCircuitHeaderOutputs
    (views : List SupplierCircuitHeaderView) : List ℕ :=
  views.map SupplierCircuitHeaderView.output

def supplierCircuitHeaderCallBits
    (views : List SupplierCircuitHeaderView) : ℕ :=
  max
    (balancedCallRequiredBits supplierCircuitHeaderRequestOutput
      (supplierCircuitHeaderRequests views))
    (((supplierCircuitHeaderRequests views).map
      supplierCircuitHeaderRequestBits).foldr max 1)

def supplierCircuitHeaderCallFuel
    (views : List SupplierCircuitHeaderView) : ℕ :=
  balancedCallFuel supplierCircuitHeaderProgram
    supplierCircuitHeaderRequestFuel
    (supplierCircuitHeaderRequests views)

private theorem header_le_foldr_max_of_mem
    {value : ℕ} {values : List ℕ} (hmem : value ∈ values) :
    value ≤ values.foldr max 1 := by
  induction values with
  | nil => simp at hmem
  | cons head rest ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact (ih hmem).trans (Nat.le_max_right _ _)

private theorem supplierCircuitHeaderOutputs_eq_map
    (views : List SupplierCircuitHeaderView) :
    (supplierCircuitHeaderRequests views).map
        supplierCircuitHeaderRequestOutput =
      supplierCircuitHeaderOutputs views := by
  simp [supplierCircuitHeaderRequests, supplierCircuitHeaderOutputs]

theorem run_supplierCircuitHeaderCallProgram
    (inputLength : ℕ) (views : List SupplierCircuitHeaderView) :
    runNPOracleProgram
        (balancedCallProgram supplierCircuitHeaderProgram)
        (supplierCircuitHeaderCallBits views)
        (supplierCircuitHeaderCallFuel views)
        (initialNPOracleState inputLength
          (encodeBalancedList
            (supplierCircuitHeaderRequests views))) =
      some
        (encodeBalancedList
          (supplierCircuitHeaderOutputs views)) := by
  rw [← supplierCircuitHeaderOutputs_eq_map]
  apply run_balancedCallProgram_from inputLength
    (supplierCircuitHeaderRequests views)
    supplierCircuitHeaderRequestFuel
    supplierCircuitHeaderRequestOutput
  · exact Nat.le_max_left _ _
  · intro request hrequest
    have hrequestBits :
        supplierCircuitHeaderRequestBits request ≤
          supplierCircuitHeaderCallBits views := by
      apply
        (header_le_foldr_max_of_mem
          (values :=
            (supplierCircuitHeaderRequests views).map
              supplierCircuitHeaderRequestBits) ?_).trans
      · exact Nat.le_max_right _ _
      · exact List.mem_map.mpr ⟨request, hrequest, rfl⟩
    rcases List.mem_map.mp hrequest with
      ⟨circuitCode, hcircuitCode, rfl⟩
    rcases List.mem_map.mp hcircuitCode with
      ⟨view, _hview, rfl⟩
    rw [supplierCircuitHeaderRequestFuel_zeroCode,
      supplierCircuitHeaderRequestOutput_zeroCode]
    rw [supplierCircuitHeaderRequestBits_zeroCode] at hrequestBits
    simp only [zeroLengthCircuitRequest, Nat.unpair_pair]
    simpa only [SupplierCircuitHeaderView.code,
      SupplierCircuitHeaderView.output] using
      run_bits_mono
        (run_supplierCircuitHeaderProgram 0 view.familyCode
          view.bottomCount view.bottomTree view.topCode)
        hrequestBits

/-! ## Direct envelope-context to header-forest program -/

def supplierCircuitRequestTreePreservingProgram : NPOracleProgram :=
  preserveRightProgram supplierCircuitRequestTreeProgram

def supplierCircuitHeaderCallPreservingProgram : NPOracleProgram :=
  preserveRightProgram <|
    balancedCallProgram supplierCircuitHeaderProgram

def supplierCircuitBatchLinkedProgram : NPOracleProgram :=
  linkPrograms supplierCircuitRequestTreePreservingProgram
    supplierCircuitHeaderCallPreservingProgram

def supplierCircuitBatchProgram : NPOracleProgram :=
  linkPrograms supplierCircuitBatchAdapterProgram
    supplierCircuitBatchLinkedProgram

def supplierCircuitRawCodes
    (views : List SupplierCircuitHeaderView) : List ℕ :=
  views.map SupplierCircuitHeaderView.code

def supplierCircuitBatchOutput
    (mode q : ℕ) (views : List SupplierCircuitHeaderView) : ℕ :=
  Nat.pair
    (encodeBalancedList (supplierCircuitHeaderOutputs views))
    (supplierCircuitBatchContext mode q)

def supplierCircuitRequestTreePreservingBits
    (mode q : ℕ) (views : List SupplierCircuitHeaderView) : ℕ :=
  preserveRightBits
    (supplierCircuitRequestTreeBits (supplierCircuitRawCodes views))
    (encodeBalancedList (supplierCircuitRawCodes views))
    (supplierCircuitBatchContext mode q)
    (encodeBalancedList (supplierCircuitHeaderRequests views))

def supplierCircuitHeaderCallPreservingBits
    (mode q : ℕ) (views : List SupplierCircuitHeaderView) : ℕ :=
  preserveRightBits
    (supplierCircuitHeaderCallBits views)
    (encodeBalancedList (supplierCircuitHeaderRequests views))
    (supplierCircuitBatchContext mode q)
    (encodeBalancedList (supplierCircuitHeaderOutputs views))

def supplierCircuitBatchBits
    (mode q : ℕ) (views : List SupplierCircuitHeaderView) : ℕ :=
  max (natBitLength q) <|
    max
      (supplierCircuitBatchAdapterBits mode q
        (encodeBalancedList (supplierCircuitRawCodes views))) <|
      max
        (supplierCircuitRequestTreePreservingBits mode q views)
        (supplierCircuitHeaderCallPreservingBits mode q views)

def supplierCircuitBatchLinkedFuel
    (views : List SupplierCircuitHeaderView) : ℕ :=
  linkFuel supplierCircuitHeaderCallPreservingProgram
    (preserveRightFuel
      (supplierCircuitRequestTreeFuel
        (supplierCircuitRawCodes views)))
    (preserveRightFuel (supplierCircuitHeaderCallFuel views))

def supplierCircuitBatchFuel
    (views : List SupplierCircuitHeaderView) : ℕ :=
  linkFuel supplierCircuitBatchLinkedProgram 7
    (supplierCircuitBatchLinkedFuel views)

@[simp] theorem supplierCircuitBatchProgram_oracleFree :
    OracleFree supplierCircuitBatchProgram := by
  apply oracleFree_linkPrograms
  · exact supplierCircuitBatchAdapterProgram_oracleFree
  · apply oracleFree_linkPrograms
    · exact preserveRightProgram_oracleFree _
        supplierCircuitRequestTreeProgram_oracleFree
    · exact preserveRightProgram_oracleFree _
        (balancedCallProgram_oracleFree
          supplierCircuitHeaderProgram_oracleFree)

theorem run_supplierCircuitBatchProgram
    (mode q : ℕ) (views : List SupplierCircuitHeaderView) :
    runNPOracleProgram supplierCircuitBatchProgram
        (supplierCircuitBatchBits mode q views)
        (supplierCircuitBatchFuel views)
        (initialNPOracleState q
          (aggregationEnvelopeContext mode q
            (encodeBalancedList
              (supplierCircuitRawCodes views)))) =
      some (supplierCircuitBatchOutput mode q views) := by
  let rawTree :=
    encodeBalancedList (supplierCircuitRawCodes views)
  let requestTree :=
    encodeBalancedList (supplierCircuitHeaderRequests views)
  let outputTree :=
    encodeBalancedList (supplierCircuitHeaderOutputs views)
  let context := supplierCircuitBatchContext mode q
  let maximumBits := supplierCircuitBatchBits mode q views
  have hqBits : natBitLength q ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength q by
      unfold natBitLength
      omega).trans hqBits
  have hadapterBits :
      supplierCircuitBatchAdapterBits mode q rawTree ≤
        maximumBits := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hrequestBits :
      supplierCircuitRequestTreePreservingBits mode q views ≤
        maximumBits := by
    exact
      (Nat.le_max_left _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hheaderBits :
      supplierCircuitHeaderCallPreservingBits mode q views ≤
        maximumBits := by
    exact
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hadapter :
      runNPOracleProgram supplierCircuitBatchAdapterProgram
          maximumBits 7
          (initialNPOracleState q
            (aggregationEnvelopeContext mode q rawTree)) =
        some (Nat.pair rawTree context) := by
    have hrun :=
      run_bits_mono
        (run_supplierCircuitBatchAdapterProgram mode q rawTree)
        hadapterBits
    simpa only [supplierCircuitBatchAdapterOutput, context] using
      hrun
  have hrequestTree :
      runNPOracleProgram supplierCircuitRequestTreePreservingProgram
          maximumBits
          (preserveRightFuel
            (supplierCircuitRequestTreeFuel
              (supplierCircuitRawCodes views)))
          (initialNPOracleState q (Nat.pair rawTree context)) =
        some (Nat.pair requestTree context) := by
    have hsource :
        runNPOracleProgram supplierCircuitRequestTreeProgram
            (supplierCircuitRequestTreeBits
              (supplierCircuitRawCodes views))
            (supplierCircuitRequestTreeFuel
              (supplierCircuitRawCodes views))
            (initialNPOracleState q rawTree) =
          some requestTree := by
      simpa only [rawTree, requestTree, supplierCircuitRawCodes,
        supplierCircuitHeaderRequests] using
        run_supplierCircuitRequestTreeProgram q
          (supplierCircuitRawCodes views)
    have hrun :=
      run_preserveRightProgram supplierCircuitRequestTreeProgram q
        (supplierCircuitRequestTreeBits
          (supplierCircuitRawCodes views))
        (supplierCircuitRequestTreeFuel
          (supplierCircuitRawCodes views))
        rawTree context requestTree
        hsource
    exact run_bits_mono hrun <| by
      simpa only [supplierCircuitRequestTreePreservingBits,
        rawTree, requestTree, context] using hrequestBits
  have hheaders :
      runNPOracleProgram supplierCircuitHeaderCallPreservingProgram
          maximumBits
          (preserveRightFuel (supplierCircuitHeaderCallFuel views))
          (initialNPOracleState q (Nat.pair requestTree context)) =
        some (Nat.pair outputTree context) := by
    have hrun :=
      run_preserveRightProgram
        (balancedCallProgram supplierCircuitHeaderProgram) q
        (supplierCircuitHeaderCallBits views)
        (supplierCircuitHeaderCallFuel views)
        requestTree context outputTree
        (run_supplierCircuitHeaderCallProgram q views)
    exact run_bits_mono hrun <| by
      simpa only [supplierCircuitHeaderCallPreservingBits,
        requestTree, outputTree, context] using hheaderBits
  have hlinked :
      runNPOracleProgram supplierCircuitBatchLinkedProgram
          maximumBits (supplierCircuitBatchLinkedFuel views)
          (initialNPOracleState q (Nat.pair rawTree context)) =
        some (Nat.pair outputTree context) := by
    exact run_linkPrograms hpositive hqBits hrequestTree hheaders
  have hrun :=
    run_linkPrograms hpositive hqBits hadapter hlinked
  simpa only [supplierCircuitBatchProgram,
    supplierCircuitBatchFuel, supplierCircuitBatchOutput,
    rawTree, outputTree, context] using hrun

/-! ## The two published typed-envelope executions -/

def symmetricCircuitHeaderView {q : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit q) :
    SupplierCircuitHeaderView where
  familyCode := encodeNat symmetricCircuitFamilyTag
  bottomCount := circuit.bottomCount
  bottomTree :=
    encodeBalancedList <|
      List.ofFn fun index =>
        encodeSupportedNormalizedGate (circuit.bottom index)
  topCode := encodeBoolList (List.ofFn circuit.top)

def thresholdCircuitHeaderView {q : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit q) :
    SupplierCircuitHeaderView where
  familyCode := encodeNat thresholdCircuitFamilyTag
  bottomCount := circuit.bottomCount
  bottomTree :=
    encodeBalancedList <|
      List.ofFn fun index =>
        encodeSupportedNormalizedGate (circuit.bottom index)
  topCode := encodeSupportedNormalizedGate circuit.top

@[simp] theorem symmetricCircuitHeaderView_code
    {q : ℕ} (circuit : NormalizedSymmetricThresholdCircuit q) :
    (symmetricCircuitHeaderView circuit).code =
      encodeNormalizedSymmetricThresholdCircuit circuit := by
  rfl

@[simp] theorem thresholdCircuitHeaderView_code
    {q : ℕ} (circuit : NormalizedThresholdThresholdCircuit q) :
    (thresholdCircuitHeaderView circuit).code =
      encodeNormalizedThresholdThresholdCircuit circuit := by
  rfl

def symmetricCircuitHeaderViews
    (request :
      FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    List SupplierCircuitHeaderView :=
  request.circuits.map symmetricCircuitHeaderView

def thresholdCircuitHeaderViews
    (request :
      FourfoldRequest NormalizedThresholdThresholdCircuit) :
    List SupplierCircuitHeaderView :=
  request.circuits.map thresholdCircuitHeaderView

@[simp] theorem symmetricCircuitRawCodes
    (request :
      FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    supplierCircuitRawCodes (symmetricCircuitHeaderViews request) =
      request.circuits.map
        encodeNormalizedSymmetricThresholdCircuit := by
  simp [supplierCircuitRawCodes, symmetricCircuitHeaderViews]

@[simp] theorem thresholdCircuitRawCodes
    (request :
      FourfoldRequest NormalizedThresholdThresholdCircuit) :
    supplierCircuitRawCodes (thresholdCircuitHeaderViews request) =
      request.circuits.map
        encodeNormalizedThresholdThresholdCircuit := by
  simp [supplierCircuitRawCodes, thresholdCircuitHeaderViews]

def supplierCircuitEnvelopeBatchProgram : NPOracleProgram :=
  linkPrograms aggregationEnvelopeLoweringProgram
    supplierCircuitBatchProgram

def supplierCircuitEnvelopeBatchFuel
    (views : List SupplierCircuitHeaderView) : ℕ :=
  linkFuel supplierCircuitBatchProgram 9
    (supplierCircuitBatchFuel views)

def supplierCircuitEnvelopeBatchBits
    (mode q : ℕ) (views : List SupplierCircuitHeaderView) : ℕ :=
  max (natBitLength q) <|
    max
      (aggregationEnvelopeLoweringBits mode q
        (encodeBalancedList (supplierCircuitRawCodes views)))
      (supplierCircuitBatchBits mode q views)

@[simp] theorem supplierCircuitEnvelopeBatchProgram_oracleFree :
    OracleFree supplierCircuitEnvelopeBatchProgram := by
  exact oracleFree_linkPrograms
    aggregationEnvelopeLoweringProgram_oracleFree
    supplierCircuitBatchProgram_oracleFree

theorem run_supplierCircuitEnvelopeBatchProgram_symmetric
    (request :
      FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    let views := symmetricCircuitHeaderViews request
    runNPOracleProgram supplierCircuitEnvelopeBatchProgram
        (supplierCircuitEnvelopeBatchBits
          symmetricCircuitFamilyTag request.q views)
        (supplierCircuitEnvelopeBatchFuel views)
        (initialNPOracleState request.q
          (fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
            encodeNormalizedSymmetricThresholdCircuit request)) =
      some
        (supplierCircuitBatchOutput symmetricCircuitFamilyTag
          request.q views) := by
  dsimp only
  let views := symmetricCircuitHeaderViews request
  let tree :=
    encodeBalancedList (supplierCircuitRawCodes views)
  let maximumBits :=
    supplierCircuitEnvelopeBatchBits
      symmetricCircuitFamilyTag request.q views
  have hqBits : natBitLength request.q ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength request.q by
      unfold natBitLength
      omega).trans hqBits
  have hloweringBits :
      aggregationEnvelopeLoweringBits symmetricCircuitFamilyTag
          request.q tree ≤
        maximumBits := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hbatchBits :
      supplierCircuitBatchBits symmetricCircuitFamilyTag
          request.q views ≤
        maximumBits := by
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlowering :
      runNPOracleProgram aggregationEnvelopeLoweringProgram
          maximumBits 9
          (initialNPOracleState request.q
            (fourfoldRequestEnvelopeOutput
              symmetricCircuitFamilyTag
              encodeNormalizedSymmetricThresholdCircuit request)) =
        some
          (aggregationEnvelopeContext symmetricCircuitFamilyTag
            request.q tree) := by
    have hrun :=
      run_bits_mono
        (run_aggregationEnvelopeLoweringProgram_symmetric
          request.q tree)
        hloweringBits
    simpa only [tree, views, fourfoldRequestEnvelopeOutput,
      symmetricCircuitRawCodes] using hrun
  have hbatch :
      runNPOracleProgram supplierCircuitBatchProgram
          maximumBits (supplierCircuitBatchFuel views)
          (initialNPOracleState request.q
            (aggregationEnvelopeContext symmetricCircuitFamilyTag
              request.q tree)) =
        some
          (supplierCircuitBatchOutput symmetricCircuitFamilyTag
            request.q views) :=
    run_bits_mono
      (run_supplierCircuitBatchProgram symmetricCircuitFamilyTag
        request.q views)
      hbatchBits
  exact run_linkPrograms hpositive hqBits hlowering hbatch

theorem run_supplierCircuitEnvelopeBatchProgram_threshold
    (request :
      FourfoldRequest NormalizedThresholdThresholdCircuit) :
    let views := thresholdCircuitHeaderViews request
    runNPOracleProgram supplierCircuitEnvelopeBatchProgram
        (supplierCircuitEnvelopeBatchBits
          thresholdCircuitFamilyTag request.q views)
        (supplierCircuitEnvelopeBatchFuel views)
        (initialNPOracleState request.q
          (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
            encodeNormalizedThresholdThresholdCircuit request)) =
      some
        (supplierCircuitBatchOutput thresholdCircuitFamilyTag
          request.q views) := by
  dsimp only
  let views := thresholdCircuitHeaderViews request
  let tree :=
    encodeBalancedList (supplierCircuitRawCodes views)
  let maximumBits :=
    supplierCircuitEnvelopeBatchBits
      thresholdCircuitFamilyTag request.q views
  have hqBits : natBitLength request.q ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength request.q by
      unfold natBitLength
      omega).trans hqBits
  have hloweringBits :
      aggregationEnvelopeLoweringBits thresholdCircuitFamilyTag
          request.q tree ≤
        maximumBits := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hbatchBits :
      supplierCircuitBatchBits thresholdCircuitFamilyTag
          request.q views ≤
        maximumBits := by
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlowering :
      runNPOracleProgram aggregationEnvelopeLoweringProgram
          maximumBits 9
          (initialNPOracleState request.q
            (fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
              encodeNormalizedThresholdThresholdCircuit request)) =
        some
          (aggregationEnvelopeContext thresholdCircuitFamilyTag
            request.q tree) := by
    have hrun :=
      run_bits_mono
        (run_aggregationEnvelopeLoweringProgram_threshold
          request.q tree)
        hloweringBits
    simpa only [tree, views, fourfoldRequestEnvelopeOutput,
      thresholdCircuitRawCodes] using hrun
  have hbatch :
      runNPOracleProgram supplierCircuitBatchProgram
          maximumBits (supplierCircuitBatchFuel views)
          (initialNPOracleState request.q
            (aggregationEnvelopeContext thresholdCircuitFamilyTag
              request.q tree)) =
        some
          (supplierCircuitBatchOutput thresholdCircuitFamilyTag
            request.q views) :=
    run_bits_mono
      (run_supplierCircuitBatchProgram thresholdCircuitFamilyTag
        request.q views)
      hbatchBits
  exact run_linkPrograms hpositive hqBits hlowering hbatch

end NearCubicWires.CanonicalSupplierCircuitBatchProgram
