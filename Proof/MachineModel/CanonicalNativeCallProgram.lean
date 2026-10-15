import Proof.Circuits.CanonicalBalancedCall
import Proof.MachineModel.PreserveRightProgram

/-!
# Canonical single native-input call

Some linked stages compute the input length required by their next callee.
The balanced-call ABI already represents such a request as
`pair(inputLength, requestCode)`.  This module supplies the unique singleton
adapter: wrap that request as a canonical balanced leaf, run the existing
balanced caller, and unwrap its single output.  It introduces no second
relocation or call protocol.
-/

namespace NearCubicWires.CanonicalNativeCallProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## Fixed singleton adapters -/

def nativeCallWrapProgram : NPOracleProgram :=
  [ .set 2 1 1
  , .pair 2 0 0 2
  , .halt 0
  ]

private def nativeCallWrapBits (request : ℕ) : ℕ :=
  max (natBitLength request)
    (natBitLength (encodeBalancedList [request]))

@[simp] private theorem nativeCallWrapProgram_oracleFree :
    OracleFree nativeCallWrapProgram := by
  rfl

private theorem run_nativeCallWrapProgram
    (outerInputLength request : ℕ) :
    runNPOracleProgram nativeCallWrapProgram
        (nativeCallWrapBits request) 3
        (initialNPOracleState outerInputLength request) =
      some (encodeBalancedList [request]) := by
  have houtput :
      natBitLength (encodeBalancedList [request]) ≤
        nativeCallWrapBits request :=
    Nat.le_max_right _ _
  have hone : natBitLength 1 ≤ nativeCallWrapBits request := by
    apply (natBitLength_mono ?_).trans houtput
    simpa [encodeBalancedList] using Nat.left_le_pair 1 request
  rw [show 3 = 2 + 1 by omega]
  rw [run_set_instruction (value := 1)
    (by rfl) rfl hone]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := encodeBalancedList [request])
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, encodeBalancedList])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        encodeBalancedList])
    houtput

def nativeCallUnwrapProgram : NPOracleProgram :=
  [ .unpairRight 0 0 1
  , .halt 0
  ]

private def nativeCallUnwrapBits (output : ℕ) : ℕ :=
  max (natBitLength (encodeBalancedList [output]))
    (natBitLength output)

@[simp] private theorem nativeCallUnwrapProgram_oracleFree :
    OracleFree nativeCallUnwrapProgram := by
  rfl

private theorem run_nativeCallUnwrapProgram
    (outerInputLength output : ℕ) :
    runNPOracleProgram nativeCallUnwrapProgram
        (nativeCallUnwrapBits output) 2
        (initialNPOracleState outerInputLength
          (encodeBalancedList [output])) =
      some output := by
  have hinput :
      natBitLength (encodeBalancedList [output]) ≤
        nativeCallUnwrapBits output :=
    Nat.le_max_left _ _
  have houtput :
      natBitLength output ≤ nativeCallUnwrapBits output :=
    Nat.le_max_right _ _
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairRight_instruction (value := output)
    (by rfl) rfl
    (by simp [initialNPOracleState, encodeBalancedList])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtput

/-! ## One explicit-input call through the balanced ABI -/

def nativeCallProgram (callee : NPOracleProgram) : NPOracleProgram :=
  linkPrograms nativeCallWrapProgram <|
    linkPrograms (balancedCallProgram callee)
      nativeCallUnwrapProgram

def nativeCallBalancedFuel
    (callee : NPOracleProgram) (calleeFuel : ℕ)
    (calleeInputLength requestCode : ℕ) : ℕ :=
  balancedCallFuel callee (fun _ => calleeFuel)
    [nativeInputRequest calleeInputLength requestCode]

def nativeCallFuel
    (callee : NPOracleProgram) (calleeFuel : ℕ)
    (calleeInputLength requestCode : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (balancedCallProgram callee)
      nativeCallUnwrapProgram)
    3 <|
    linkFuel nativeCallUnwrapProgram
      (nativeCallBalancedFuel callee calleeFuel
        calleeInputLength requestCode)
      2

def nativeCallBits
    (outerInputLength calleeInputLength requestCode output
      calleeBits : ℕ) : ℕ :=
  let request := nativeInputRequest calleeInputLength requestCode
  max (natBitLength outerInputLength) <|
    max (nativeCallWrapBits request) <|
      max
        (balancedCallRequiredBits (fun _ => output) [request]) <|
        max calleeBits (nativeCallUnwrapBits output)

@[simp] theorem nativeCallProgram_oracleFree
    {callee : NPOracleProgram} (hcallee : OracleFree callee) :
    OracleFree (nativeCallProgram callee) := by
  apply oracleFree_linkPrograms
  · exact nativeCallWrapProgram_oracleFree
  · apply oracleFree_linkPrograms
    · exact balancedCallProgram_oracleFree hcallee
    · exact nativeCallUnwrapProgram_oracleFree

/-- Exact execution with a callee input length computed by an earlier stage.
`outerInputLength` remains the linked program's public length; only the
canonical request atom controls the relocated callee's `r1`. -/
theorem run_nativeCallProgram
    (callee : NPOracleProgram)
    (outerInputLength calleeInputLength requestCode output
      calleeBits calleeFuel : ℕ)
    (hcallee :
      runNPOracleProgram callee calleeBits calleeFuel
          (initialNPOracleState calleeInputLength requestCode) =
        some output) :
    runNPOracleProgram (nativeCallProgram callee)
        (nativeCallBits outerInputLength calleeInputLength
          requestCode output calleeBits)
        (nativeCallFuel callee calleeFuel
          calleeInputLength requestCode)
        (initialNPOracleState outerInputLength
          (nativeInputRequest calleeInputLength requestCode)) =
      some output := by
  let request := nativeInputRequest calleeInputLength requestCode
  let requestTree := encodeBalancedList [request]
  let outputTree := encodeBalancedList [output]
  let maximumBits :=
    nativeCallBits outerInputLength calleeInputLength
      requestCode output calleeBits
  let balancedFuel :=
    nativeCallBalancedFuel callee calleeFuel
      calleeInputLength requestCode
  have houterBits :
      natBitLength outerInputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength outerInputLength by
      unfold natBitLength
      omega).trans houterBits
  have hwrapBits :
      nativeCallWrapBits request ≤ maximumBits := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hbalancedBits :
      balancedCallRequiredBits (fun _ => output) [request] ≤
        maximumBits := by
    exact
      (Nat.le_max_left _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcalleeBits : calleeBits ≤ maximumBits := by
    exact
      (Nat.le_max_left _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hunwrapBits :
      nativeCallUnwrapBits output ≤ maximumBits := by
    exact
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hwrap :
      runNPOracleProgram nativeCallWrapProgram maximumBits 3
          (initialNPOracleState outerInputLength request) =
        some requestTree := by
    exact run_bits_mono
      (run_nativeCallWrapProgram outerInputLength request)
      hwrapBits
  have hbalanced :
      runNPOracleProgram (balancedCallProgram callee)
          maximumBits balancedFuel
          (initialNPOracleState outerInputLength requestTree) =
        some outputTree := by
    have hrun :
        runNPOracleProgram (balancedCallProgram callee)
            maximumBits
            (balancedCallFuel callee (fun _ => calleeFuel) [request])
            (initialNPOracleState outerInputLength
              (encodeBalancedList [request])) =
          some
            (encodeBalancedList
              ([request].map (fun _ => output))) := by
      apply run_balancedCallProgram_from outerInputLength
        [request] (fun _ => calleeFuel) (fun _ => output)
        hbalancedBits
      intro candidate hcandidate
      have hequal : candidate = request := by
        simpa using hcandidate
      subst candidate
      simpa only [request, nativeInputRequest,
        Nat.unpair_pair] using
        (run_bits_mono hcallee hcalleeBits)
    simpa only [balancedFuel, nativeCallBalancedFuel,
      requestTree, outputTree, request, List.map_cons,
      List.map_nil] using hrun
  have hunwrap :
      runNPOracleProgram nativeCallUnwrapProgram maximumBits 2
          (initialNPOracleState outerInputLength outputTree) =
        some output := by
    exact run_bits_mono
      (run_nativeCallUnwrapProgram outerInputLength output)
      hunwrapBits
  have hinner :
      runNPOracleProgram
          (linkPrograms (balancedCallProgram callee)
            nativeCallUnwrapProgram)
          maximumBits
          (linkFuel nativeCallUnwrapProgram balancedFuel 2)
          (initialNPOracleState outerInputLength requestTree) =
        some output :=
    run_linkPrograms hpositive houterBits hbalanced hunwrap
  have hrun :=
    run_linkPrograms hpositive houterBits hwrap hinner
  simpa only [nativeCallProgram, nativeCallFuel, balancedFuel,
    request, requestTree] using hrun

/-! ## Explicit-input call with retained context -/

/-- Reframe `pair(requestCode, pair(calleeInputLength, context))` for the
singleton native caller.  The computed length remains beside the context so
later stages need not recover it from the imported runner's opaque output. -/
def nativeContextCallAdapterProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .pair 4 2 5 4
  , .pair 5 3 0 5
  , .halt 0
  ]

private def nativeContextCallAdapterBits
    (calleeInputLength requestCode context : ℕ) : ℕ :=
  max
    (natBitLength
      (Nat.pair requestCode (Nat.pair calleeInputLength context)))
    (natBitLength
      (Nat.pair (nativeInputRequest calleeInputLength requestCode)
        (Nat.pair calleeInputLength context)))

@[simp] private theorem nativeContextCallAdapterProgram_oracleFree :
    OracleFree nativeContextCallAdapterProgram := by
  rfl

private theorem run_nativeContextCallAdapterProgram
    (outerInputLength calleeInputLength requestCode context : ℕ) :
    runNPOracleProgram nativeContextCallAdapterProgram
        (nativeContextCallAdapterBits calleeInputLength requestCode context)
        6
        (initialNPOracleState outerInputLength
          (Nat.pair requestCode
            (Nat.pair calleeInputLength context))) =
      some
        (Nat.pair (nativeInputRequest calleeInputLength requestCode)
          (Nat.pair calleeInputLength context)) := by
  let retained := Nat.pair calleeInputLength context
  let request := nativeInputRequest calleeInputLength requestCode
  let input := Nat.pair requestCode retained
  let output := Nat.pair request retained
  let maximumBits :=
    nativeContextCallAdapterBits calleeInputLength requestCode context
  have hinput : natBitLength input ≤ maximumBits :=
    Nat.le_max_left _ _
  have houtput : natBitLength output ≤ maximumBits :=
    Nat.le_max_right _ _
  have hrequestCode : natBitLength requestCode ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.left_le_pair requestCode retained)).trans hinput
  have hretained : natBitLength retained ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.right_le_pair requestCode retained)).trans hinput
  have hcalleeInputLength :
      natBitLength calleeInputLength ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.left_le_pair calleeInputLength context)).trans hretained
  have hrequest : natBitLength request ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.left_le_pair request retained)).trans houtput
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := requestCode)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hrequestCode]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := retained)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, retained])
    hretained]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := calleeInputLength)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, retained])
    hcalleeInputLength]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := request)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, request,
        nativeInputRequest])
    hrequest]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output,
      request, retained, nativeInputRequest])
    houtput

/-- The unique contextual form of `nativeCallProgram`.  It adds only a fixed
framing adapter and the standard context-preserving wrapper. -/
def nativeContextCallProgram (callee : NPOracleProgram) : NPOracleProgram :=
  linkPrograms nativeContextCallAdapterProgram <|
    preserveRightProgram (nativeCallProgram callee)

def nativeContextCallFuel
    (callee : NPOracleProgram) (calleeFuel : ℕ)
    (calleeInputLength requestCode : ℕ) : ℕ :=
  linkFuel
    (preserveRightProgram (nativeCallProgram callee))
    6 <|
    preserveRightFuel
      (nativeCallFuel callee calleeFuel calleeInputLength requestCode)

def nativeContextCallBits
    (outerInputLength calleeInputLength requestCode context output
      calleeBits : ℕ) : ℕ :=
  let retained := Nat.pair calleeInputLength context
  max (natBitLength outerInputLength) <|
    max
      (nativeContextCallAdapterBits
        calleeInputLength requestCode context)
      (preserveRightBits
        (nativeCallBits outerInputLength calleeInputLength
          requestCode output calleeBits)
        (nativeInputRequest calleeInputLength requestCode)
        retained output)

@[simp] theorem nativeContextCallProgram_oracleFree
    {callee : NPOracleProgram} (hcallee : OracleFree callee) :
    OracleFree (nativeContextCallProgram callee) := by
  apply oracleFree_linkPrograms
  · exact nativeContextCallAdapterProgram_oracleFree
  · exact preserveRightProgram_oracleFree _
      (nativeCallProgram_oracleFree hcallee)

theorem run_nativeContextCallProgram
    (callee : NPOracleProgram)
    (outerInputLength calleeInputLength requestCode context output
      calleeBits calleeFuel : ℕ)
    (hcallee :
      runNPOracleProgram callee calleeBits calleeFuel
          (initialNPOracleState calleeInputLength requestCode) =
        some output) :
    runNPOracleProgram (nativeContextCallProgram callee)
        (nativeContextCallBits outerInputLength calleeInputLength
          requestCode context output calleeBits)
        (nativeContextCallFuel callee calleeFuel
          calleeInputLength requestCode)
        (initialNPOracleState outerInputLength
          (Nat.pair requestCode
            (Nat.pair calleeInputLength context))) =
      some
        (Nat.pair output (Nat.pair calleeInputLength context)) := by
  let retained := Nat.pair calleeInputLength context
  let request := nativeInputRequest calleeInputLength requestCode
  let framed := Nat.pair request retained
  let maximumBits :=
    nativeContextCallBits outerInputLength calleeInputLength
      requestCode context output calleeBits
  have houterBits :
      natBitLength outerInputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength outerInputLength by
      unfold natBitLength
      omega).trans houterBits
  have hadapterBits :
      nativeContextCallAdapterBits calleeInputLength requestCode context ≤
        maximumBits := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hpreservingBits :
      preserveRightBits
          (nativeCallBits outerInputLength calleeInputLength
            requestCode output calleeBits)
          request retained output ≤
        maximumBits := by
    exact
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hadapter :
      runNPOracleProgram nativeContextCallAdapterProgram maximumBits 6
          (initialNPOracleState outerInputLength
            (Nat.pair requestCode retained)) =
        some framed := by
    exact run_bits_mono
      (run_nativeContextCallAdapterProgram outerInputLength
        calleeInputLength requestCode context)
      hadapterBits
  have hnative :=
    run_nativeCallProgram callee outerInputLength calleeInputLength
      requestCode output calleeBits calleeFuel hcallee
  have hpreserving :
      runNPOracleProgram
          (preserveRightProgram (nativeCallProgram callee))
          maximumBits
          (preserveRightFuel
            (nativeCallFuel callee calleeFuel
              calleeInputLength requestCode))
          (initialNPOracleState outerInputLength framed) =
        some (Nat.pair output retained) := by
    exact run_bits_mono
      (run_preserveRightProgram (nativeCallProgram callee)
        outerInputLength
        (nativeCallBits outerInputLength calleeInputLength
          requestCode output calleeBits)
        (nativeCallFuel callee calleeFuel
          calleeInputLength requestCode)
        request retained output hnative)
      hpreservingBits
  have hrun :=
    run_linkPrograms hpositive houterBits hadapter hpreserving
  simpa only [nativeContextCallProgram, nativeContextCallFuel,
    retained, request, framed] using hrun

end NearCubicWires.CanonicalNativeCallProgram
