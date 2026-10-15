import Proof.Circuits.CanonicalBalancedCall
import Proof.MachineModel.CanonicalBalancedLengthProgram
import Proof.MachineModel.CanonicalBalancedValidationProgram
import Proof.MachineModel.CanonicalNativeEqualityProgram
import Proof.MachineModel.PreserveRightProgram
import Proof.Foundations.VerifiedLinker

/-!
# Guarded canonical-balanced validation map

Nested recovery records contain several balanced lists whose atoms are
validated by different fixed callees.  This module supplies one structural
control shell for all of them.  It first proves the public balanced encoding,
retains that result beside the original bytes, and only then maps a caller-
selected fixed program over the atoms through the sole balanced-call ABI.

Malformed syntax is mapped to the canonical empty tree while a retained zero
flag records the rejection.  Consequently later stages can execute total list
machinery without treating malformed input as an accepted empty list.
-/

namespace NearCubicWires.CanonicalBalancedValidationMapProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

def balancedValidationMapCodes (raw : ℕ) : List ℕ :=
  (decodeBalancedList raw).getD []

def balancedValidationMapFlag (raw : ℕ) : ℕ :=
  balancedCanonicalityOutput raw

def balancedValidationMapContext (raw : ℕ) : ℕ :=
  Nat.pair (balancedValidationMapFlag raw) raw

def balancedValidationMapGuardedCode (raw : ℕ) : ℕ :=
  if balancedValidationMapFlag raw = 0 then 0 else raw

def balancedValidationMapGuardOutput (raw : ℕ) : ℕ :=
  Nat.pair (balancedValidationMapGuardedCode raw)
    (balancedValidationMapContext raw)

def balancedValidationMapDuplicateProgram : NPOracleProgram :=
  [.pair 0 0 0 1, .halt 0]

private def balancedValidationMapDuplicateBits (raw : ℕ) : ℕ :=
  max (natBitLength raw) (natBitLength (Nat.pair raw raw))

@[simp] private theorem balancedValidationMapDuplicateProgram_oracleFree :
    OracleFree balancedValidationMapDuplicateProgram := by
  rfl

private theorem run_balancedValidationMapDuplicateProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram balancedValidationMapDuplicateProgram
        (balancedValidationMapDuplicateBits raw) 2
        (initialNPOracleState inputLength raw) =
      some (Nat.pair raw raw) := by
  have houtput :
      natBitLength (Nat.pair raw raw) ≤
        balancedValidationMapDuplicateBits raw :=
    Nat.le_max_right _ _
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (program := balancedValidationMapDuplicateProgram)
    (maximumBits := balancedValidationMapDuplicateBits raw)
    (fuel := 1) (pc := 0) (left := 0) (right := 0)
    (destination := 0) (next := 1) (value := Nat.pair raw raw)
    (by rfl) rfl (by simp [initialNPOracleState]) houtput]
  exact run_halt_instruction
    (program := balancedValidationMapDuplicateProgram)
    (maximumBits := balancedValidationMapDuplicateBits raw)
    (fuel := 0) (pc := 1) (outputRegister := 0)
    (value := Nat.pair raw raw)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

def balancedValidationMapGuardGateProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .pair 2 3 4 3
  , .branchZero 2 6 4
  , .pair 3 4 0 7
  , .halt 0
  , .set 5 0 8
  , .halt 0
  , .pair 5 4 0 5
  ]

@[simp] private theorem balancedValidationMapGuardGateProgram_oracleFree :
    OracleFree balancedValidationMapGuardGateProgram := by
  rfl

def balancedValidationMapGuardGateFuel : ℕ := 7

private def balancedValidationMapGuardGateValues (raw : ℕ) : List ℕ :=
  let flag := balancedValidationMapFlag raw
  [ Nat.pair flag raw
  , flag
  , raw
  , Nat.pair flag raw
  , 0
  , balancedValidationMapGuardOutput raw
  ]

private def balancedValidationMapGuardGateBits (raw : ℕ) : ℕ :=
  (balancedValidationMapGuardGateValues raw).map natBitLength
    |>.foldr max 1

private theorem bitLength_le_foldr_max_of_mem
    {values : List ℕ} {value : ℕ} (hvalue : value ∈ values) :
    natBitLength value ≤
      (values.map natBitLength).foldr max 1 := by
  induction values with
  | nil => simp at hvalue
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at hvalue
      simp only [List.map_cons, List.foldr_cons]
      rcases hvalue with rfl | htail
      · exact le_max_left _ _
      · exact (inductionHypothesis htail).trans (le_max_right _ _)

private theorem run_balancedValidationMapGuardGateProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram balancedValidationMapGuardGateProgram
        (balancedValidationMapGuardGateBits raw)
        balancedValidationMapGuardGateFuel
        (initialNPOracleState inputLength
          (Nat.pair (balancedValidationMapFlag raw) raw)) =
      some (balancedValidationMapGuardOutput raw) := by
  let flag := balancedValidationMapFlag raw
  let context := Nat.pair flag raw
  let maximumBits := balancedValidationMapGuardGateBits raw
  have hbits :
      ∀ value ∈ balancedValidationMapGuardGateValues raw,
        natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact bitLength_le_foldr_max_of_mem hvalue
  have hflag : natBitLength flag ≤ maximumBits :=
    hbits flag (by
      simp [balancedValidationMapGuardGateValues, flag])
  have hraw : natBitLength raw ≤ maximumBits :=
    hbits raw (by
      simp [balancedValidationMapGuardGateValues])
  have hcontext : natBitLength context ≤ maximumBits :=
    hbits context (by
      simp [balancedValidationMapGuardGateValues, context, flag])
  have hzero : natBitLength 0 ≤ maximumBits :=
    hbits 0 (by
      simp [balancedValidationMapGuardGateValues])
  have houtput :
      natBitLength (balancedValidationMapGuardOutput raw) ≤ maximumBits :=
    hbits (balancedValidationMapGuardOutput raw) (by
      simp [balancedValidationMapGuardGateValues])
  rw [show balancedValidationMapGuardGateFuel = 6 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (program := balancedValidationMapGuardGateProgram)
    (maximumBits := maximumBits) (fuel := 6)
    (pc := 0) (source := 0) (destination := 2) (next := 1)
    (value := flag) (by rfl) rfl
    (by simp [initialNPOracleState, flag]) hflag]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := balancedValidationMapGuardGateProgram)
    (maximumBits := maximumBits) (fuel := 5)
    (pc := 1) (source := 0) (destination := 3) (next := 2)
    (value := raw) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, flag]) hraw]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction
    (program := balancedValidationMapGuardGateProgram)
    (maximumBits := maximumBits) (fuel := 4)
    (pc := 2) (left := 2) (right := 3) (destination := 4) (next := 3)
    (value := context) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, context]) hcontext]
  rw [show 4 = 3 + 1 by omega]
  rw [run_branchZero_instruction
    (program := balancedValidationMapGuardGateProgram)
    (maximumBits := maximumBits) (fuel := 3)
    (pc := 3) (register := 2) (zeroTarget := 6)
    (nonzeroTarget := 4) (by rfl) rfl]
  by_cases hflagZero : flag = 0
  · rw [show
      (((((initialNPOracleState inputLength (Nat.pair flag raw)).write
        2 flag).jump 1 |>.write 3 raw).jump 2 |>.write 4 context).jump 3).registers
          2 = 0 by
        simp [NPOracleState.write, NPOracleState.jump, hflagZero]]
    rw [if_pos rfl]
    rw [show 3 = 2 + 1 by omega]
    rw [run_set_instruction
      (program := balancedValidationMapGuardGateProgram)
      (maximumBits := maximumBits) (fuel := 2)
      (pc := 6) (register := 5) (value := 0) (next := 8)
      (by rfl) rfl hzero]
    rw [show 2 = 1 + 1 by omega]
    rw [run_pair_instruction
      (program := balancedValidationMapGuardGateProgram)
      (maximumBits := maximumBits) (fuel := 1)
      (pc := 8) (left := 5) (right := 4) (destination := 0) (next := 5)
      (value := balancedValidationMapGuardOutput raw)
      (by rfl) rfl
      (by
        simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump, balancedValidationMapGuardOutput,
          balancedValidationMapGuardedCode,
          balancedValidationMapContext, flag, context, hflagZero])
      houtput]
    exact run_halt_instruction
      (program := balancedValidationMapGuardGateProgram)
      (maximumBits := maximumBits) (fuel := 0)
      (pc := 5) (outputRegister := 0)
      (value := balancedValidationMapGuardOutput raw)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      houtput
  · rw [show
      (((((initialNPOracleState inputLength (Nat.pair flag raw)).write
        2 flag).jump 1 |>.write 3 raw).jump 2 |>.write 4 context).jump 3).registers
          2 = flag by
        simp [NPOracleState.write, NPOracleState.jump]]
    rw [if_neg hflagZero]
    rw [show 3 = 2 + 1 by omega]
    rw [run_pair_instruction
      (program := balancedValidationMapGuardGateProgram)
      (maximumBits := maximumBits) (fuel := 2)
      (pc := 4) (left := 3) (right := 4) (destination := 0) (next := 7)
      (value := balancedValidationMapGuardOutput raw)
      (by rfl) rfl
      (by
        simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump, balancedValidationMapGuardOutput,
          balancedValidationMapGuardedCode,
          balancedValidationMapContext, flag, context, hflagZero])
      houtput]
    exact run_halt_instruction
      (program := balancedValidationMapGuardGateProgram)
      (maximumBits := maximumBits) (fuel := 1)
      (pc := 7) (outputRegister := 0)
      (value := balancedValidationMapGuardOutput raw)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      houtput

def balancedValidationMapGuardProgram : NPOracleProgram :=
  linkPrograms
    (linkPrograms balancedValidationMapDuplicateProgram <|
      preserveRightProgram balancedCanonicalityProgram)
    balancedValidationMapGuardGateProgram

@[simp] theorem balancedValidationMapGuardProgram_oracleFree :
    OracleFree balancedValidationMapGuardProgram := by
  exact oracleFree_linkPrograms
    (oracleFree_linkPrograms
      balancedValidationMapDuplicateProgram_oracleFree <|
        preserveRightProgram_oracleFree balancedCanonicalityProgram
          balancedCanonicalityProgram_oracleFree)
    balancedValidationMapGuardGateProgram_oracleFree

def balancedValidationMapGuardFuel (raw : ℕ) : ℕ :=
  linkFuel balancedValidationMapGuardGateProgram
    (linkFuel (preserveRightProgram balancedCanonicalityProgram) 2 <|
      preserveRightFuel (balancedCanonicalityFuel raw))
    balancedValidationMapGuardGateFuel

def balancedValidationMapGuardBits (inputLength raw : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (balancedValidationMapDuplicateBits raw) <|
      max
        (preserveRightBits
          (balancedCanonicalityBits inputLength raw)
          raw raw (balancedValidationMapFlag raw))
        (balancedValidationMapGuardGateBits raw)

theorem run_balancedValidationMapGuardProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram balancedValidationMapGuardProgram
        (balancedValidationMapGuardBits inputLength raw)
        (balancedValidationMapGuardFuel raw)
        (initialNPOracleState inputLength raw) =
      some (balancedValidationMapGuardOutput raw) := by
  let flag := balancedValidationMapFlag raw
  let maximumBits := balancedValidationMapGuardBits inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    exact Nat.le_max_left _ _
  have hlength : natBitLength inputLength ≤ maximumBits := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hduplicateBits :
      balancedValidationMapDuplicateBits raw ≤ maximumBits := by
    exact (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcanonicalityBits :
      preserveRightBits
          (balancedCanonicalityBits inputLength raw)
          raw raw flag ≤ maximumBits := by
    exact (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hgateBits :
      balancedValidationMapGuardGateBits raw ≤ maximumBits := by
    exact (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hduplicate :
      runNPOracleProgram balancedValidationMapDuplicateProgram maximumBits 2
          (initialNPOracleState inputLength raw) =
        some (Nat.pair raw raw) :=
    run_bits_mono
      (run_balancedValidationMapDuplicateProgram inputLength raw)
      hduplicateBits
  have hcanonicality :
      runNPOracleProgram
          (preserveRightProgram balancedCanonicalityProgram)
          maximumBits
          (preserveRightFuel (balancedCanonicalityFuel raw))
          (initialNPOracleState inputLength (Nat.pair raw raw)) =
        some (Nat.pair flag raw) := by
    exact run_bits_mono
      (run_preserveRightProgram balancedCanonicalityProgram inputLength
        (balancedCanonicalityBits inputLength raw)
        (balancedCanonicalityFuel raw) raw raw flag
        (run_balancedCanonicalityProgram inputLength raw))
      hcanonicalityBits
  have hprefix :=
    run_linkPrograms hpositive hlength hduplicate hcanonicality
  have hgate :=
    run_bits_mono
      (run_balancedValidationMapGuardGateProgram inputLength raw)
      hgateBits
  have hrun :=
    run_linkPrograms hpositive hlength hprefix hgate
  simpa only [balancedValidationMapGuardProgram,
    balancedValidationMapGuardFuel, flag] using hrun

theorem balancedValidationMapGuardedCode_eq
    (raw : ℕ) :
    balancedValidationMapGuardedCode raw =
      encodeBalancedList (balancedValidationMapCodes raw) := by
  cases hdecode : decodeBalancedList raw with
  | none =>
      have hflag :
          balancedValidationMapFlag raw = 0 := by
        exact (balancedCanonicalityOutput_eq_zero_iff raw).2 hdecode
      change
        (if balancedValidationMapFlag raw = 0 then 0 else raw) =
          encodeBalancedList ((decodeBalancedList raw).getD [])
      rw [hflag]
      simp only [if_pos, hdecode, Option.getD_none]
      simp [encodeBalancedList]
  | some codes =>
      have hflag :
          balancedValidationMapFlag raw = 1 := by
        apply (balancedCanonicalityOutput_eq_one_iff raw).2
        simp [hdecode]
      have hcode : encodeBalancedList codes = raw :=
        encodeBalancedList_of_decode hdecode
      simp [balancedValidationMapGuardedCode,
        balancedValidationMapCodes, hdecode, hflag, hcode]

/-! ## One guarded balanced map -/

def balancedValidationMapRequests
    (inputLength raw : ℕ) : List ℕ :=
  (balancedValidationMapCodes raw).map
    (nativeInputRequest inputLength)

def balancedValidationMapOutputs
    (inputLength raw : ℕ) (output : ℕ → ℕ) : List ℕ :=
  (balancedValidationMapRequests inputLength raw).map output

def balancedValidationMapOutput
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  Nat.pair
    (encodeBalancedList
      (balancedValidationMapOutputs inputLength raw output))
    (balancedValidationMapContext raw)

def balancedValidationMapProgram
    (callee : NPOracleProgram) : NPOracleProgram :=
  linkPrograms balancedValidationMapGuardProgram <|
    linkPrograms
      (preserveRightProgram nativeInputRequestTreeProgram)
      (preserveRightProgram (balancedCallProgram callee))

@[simp] theorem balancedValidationMapProgram_oracleFree
    (callee : NPOracleProgram) (hcallee : OracleFree callee) :
    OracleFree (balancedValidationMapProgram callee) := by
  exact oracleFree_linkPrograms
    balancedValidationMapGuardProgram_oracleFree <|
      oracleFree_linkPrograms
        (preserveRightProgram_oracleFree nativeInputRequestTreeProgram
          nativeInputRequestTreeProgram_oracleFree)
        (preserveRightProgram_oracleFree (balancedCallProgram callee)
          (balancedCallProgram_oracleFree hcallee))

private theorem member_le_foldr_max
    {value : ℕ} {values : List ℕ} (hvalue : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => simp at hvalue
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp hvalue with rfl | htail
      · exact le_max_left _ _
      · exact (inductionHypothesis htail).trans (le_max_right _ _)

def balancedValidationMapCalleeBits
    (inputLength raw : ℕ) (calleeBits : ℕ → ℕ) : ℕ :=
  ((balancedValidationMapRequests inputLength raw).map calleeBits)
    |>.foldr max 0

def balancedValidationMapCallBits
    (inputLength raw : ℕ)
    (calleeBits output : ℕ → ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (balancedValidationMapCalleeBits inputLength raw calleeBits)
      (balancedCallRequiredBits output
        (balancedValidationMapRequests inputLength raw))

def balancedValidationMapFuel
    (callee : NPOracleProgram) (calleeFuel : ℕ → ℕ)
    (inputLength raw : ℕ) : ℕ :=
  let codes := balancedValidationMapCodes raw
  let requests := balancedValidationMapRequests inputLength raw
  linkFuel
    (linkPrograms
      (preserveRightProgram nativeInputRequestTreeProgram)
      (preserveRightProgram (balancedCallProgram callee)))
    (balancedValidationMapGuardFuel raw) <|
      linkFuel (preserveRightProgram (balancedCallProgram callee))
        (preserveRightFuel (nativeInputRequestTreeFuel codes))
        (preserveRightFuel
          (balancedCallFuel callee calleeFuel requests))

def balancedValidationMapBits
    (calleeBits output : ℕ → ℕ)
    (inputLength raw : ℕ) : ℕ :=
  let codes := balancedValidationMapCodes raw
  let requests := balancedValidationMapRequests inputLength raw
  let outputs := balancedValidationMapOutputs inputLength raw output
  let context := balancedValidationMapContext raw
  let requestCode := encodeBalancedList requests
  let outputCode := encodeBalancedList outputs
  max 1 <| max (natBitLength inputLength) <|
    max (balancedValidationMapGuardBits inputLength raw) <|
      max
        (preserveRightBits
          (nativeInputRequestTreeBits inputLength codes)
          (balancedValidationMapGuardedCode raw) context requestCode)
        (preserveRightBits
          (balancedValidationMapCallBits
            inputLength raw calleeBits output)
          requestCode context outputCode)

theorem run_balancedValidationMapProgram
    (callee : NPOracleProgram)
    (calleeBits calleeFuel output : ℕ → ℕ)
    (inputLength raw : ℕ)
    (hexec :
      ∀ request,
        request ∈ balancedValidationMapRequests inputLength raw →
          runNPOracleProgram callee (calleeBits request)
              (calleeFuel request)
              (initialNPOracleState
                (Nat.unpair request).1 (Nat.unpair request).2) =
            some (output request)) :
    runNPOracleProgram (balancedValidationMapProgram callee)
        (balancedValidationMapBits calleeBits output
          inputLength raw)
        (balancedValidationMapFuel callee calleeFuel inputLength raw)
        (initialNPOracleState inputLength raw) =
      some (balancedValidationMapOutput inputLength raw output) := by
  let codes := balancedValidationMapCodes raw
  let requests := balancedValidationMapRequests inputLength raw
  let outputs := balancedValidationMapOutputs inputLength raw output
  let context := balancedValidationMapContext raw
  let guardedCode := balancedValidationMapGuardedCode raw
  let requestCode := encodeBalancedList requests
  let outputCode := encodeBalancedList outputs
  let callBits :=
    balancedValidationMapCallBits inputLength raw calleeBits output
  let maximumBits :=
    balancedValidationMapBits calleeBits output inputLength raw
  have hpositive : 1 ≤ maximumBits := by
    exact Nat.le_max_left _ _
  have hlength : natBitLength inputLength ≤ maximumBits := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hguardBits :
      balancedValidationMapGuardBits inputLength raw ≤ maximumBits := by
    exact (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hrequestBits :
      preserveRightBits
          (nativeInputRequestTreeBits inputLength codes)
          guardedCode context requestCode ≤ maximumBits := by
    exact (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcallBits :
      preserveRightBits callBits requestCode context outputCode ≤
        maximumBits := by
    exact (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hguard :=
    run_bits_mono
      (run_balancedValidationMapGuardProgram inputLength raw)
      hguardBits
  have hrequestsSource :
      runNPOracleProgram nativeInputRequestTreeProgram
          (nativeInputRequestTreeBits inputLength codes)
          (nativeInputRequestTreeFuel codes)
          (initialNPOracleState inputLength guardedCode) =
        some requestCode := by
    dsimp only [guardedCode]
    rw [balancedValidationMapGuardedCode_eq raw]
    simpa [codes, requests, balancedValidationMapRequests,
      requestCode] using
      run_nativeInputRequestTreeProgram inputLength codes
  have hrequests :
      runNPOracleProgram
          (preserveRightProgram nativeInputRequestTreeProgram)
          maximumBits
          (preserveRightFuel (nativeInputRequestTreeFuel codes))
          (initialNPOracleState inputLength
            (Nat.pair guardedCode context)) =
        some (Nat.pair requestCode context) := by
    exact run_bits_mono
      (run_preserveRightProgram nativeInputRequestTreeProgram inputLength
        (nativeInputRequestTreeBits inputLength codes)
        (nativeInputRequestTreeFuel codes)
        guardedCode context requestCode hrequestsSource)
      hrequestBits
  have hcallRequired :
      balancedCallRequiredBits output requests ≤ callBits := by
    exact (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcalleeBound :
      ∀ request, request ∈ requests →
        calleeBits request ≤ callBits := by
    intro request hrequest
    apply (member_le_foldr_max
      (List.mem_map.mpr ⟨request, hrequest, rfl⟩)).trans
    exact (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcallSource :
      runNPOracleProgram (balancedCallProgram callee) callBits
          (balancedCallFuel callee calleeFuel requests)
          (initialNPOracleState inputLength requestCode) =
        some outputCode := by
    have hrun :
        runNPOracleProgram (balancedCallProgram callee) callBits
            (balancedCallFuel callee calleeFuel requests)
            (initialNPOracleState inputLength
              (encodeBalancedList requests)) =
          some (encodeBalancedList (requests.map output)) := by
      apply run_balancedCallProgram_from inputLength requests
        calleeFuel output hcallRequired
      intro request hrequest
      exact run_bits_mono
        (hexec request (by simpa [requests] using hrequest))
        (hcalleeBound request hrequest)
    simpa [requestCode, outputCode, outputs,
      balancedValidationMapOutputs, requests] using hrun
  have hcall :
      runNPOracleProgram
          (preserveRightProgram (balancedCallProgram callee))
          maximumBits
          (preserveRightFuel
            (balancedCallFuel callee calleeFuel requests))
          (initialNPOracleState inputLength
            (Nat.pair requestCode context)) =
        some (Nat.pair outputCode context) := by
    exact run_bits_mono
      (run_preserveRightProgram (balancedCallProgram callee)
        inputLength callBits
        (balancedCallFuel callee calleeFuel requests)
        requestCode context outputCode hcallSource)
      hcallBits
  have htail :=
    run_linkPrograms hpositive hlength hrequests hcall
  have hrun :=
    run_linkPrograms hpositive hlength hguard htail
  simpa [balancedValidationMapProgram, balancedValidationMapFuel,
    balancedValidationMapOutput, maximumBits, codes, requests, outputs,
    context, guardedCode, requestCode, outputCode, callBits] using hrun

/-- A successful guarded map's complete handoff value fits its declared width.
Keep this frame fact beside the generic controller so downstream link proofs do
not unfold the controller's nested width envelope. -/
theorem balancedValidationMapOutput_bits_le
    (callee : NPOracleProgram)
    (calleeBits calleeFuel output : ℕ → ℕ)
    (inputLength raw : ℕ)
    (hexec :
      ∀ request,
        request ∈ balancedValidationMapRequests inputLength raw →
          runNPOracleProgram callee (calleeBits request)
              (calleeFuel request)
              (initialNPOracleState
                (Nat.unpair request).1 (Nat.unpair request).2) =
            some (output request)) :
    natBitLength (balancedValidationMapOutput inputLength raw output) ≤
      balancedValidationMapBits calleeBits output inputLength raw :=
  run_output_bounded
    (run_balancedValidationMapProgram callee calleeBits calleeFuel output
      inputLength raw hexec)

/-! ## All-valid continuation

The mapped tree has the same shape as the canonical source tree.  Its length
is nevertheless derived by the existing executable balanced-length program;
the shared generic nonzero counter then proves that every callee result
accepted.  The retained structural flag is checked last, so malformed input
cannot be confused with the valid empty list. -/

def balancedValidationAllLengthInput
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  let outputCode :=
    encodeBalancedList
      (balancedValidationMapOutputs inputLength raw output)
  Nat.pair outputCode
    (Nat.pair outputCode (balancedValidationMapContext raw))

def balancedValidationAllLengthPrepareProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .pair 2 3 4 3
  , .pair 2 4 0 4
  , .halt 0
  ]

@[simp] private theorem
    balancedValidationAllLengthPrepareProgram_oracleFree :
    OracleFree balancedValidationAllLengthPrepareProgram := by
  rfl

private def balancedValidationAllLengthPrepareBits
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  let outputCode :=
    encodeBalancedList
      (balancedValidationMapOutputs inputLength raw output)
  let context := balancedValidationMapContext raw
  [ Nat.pair outputCode context
  , outputCode
  , context
  , Nat.pair outputCode context
  , balancedValidationAllLengthInput inputLength raw output
  ].map natBitLength |>.foldr max 1

private theorem run_balancedValidationAllLengthPrepareProgram
    (inputLength raw : ℕ) (output : ℕ → ℕ) :
    runNPOracleProgram balancedValidationAllLengthPrepareProgram
        (balancedValidationAllLengthPrepareBits inputLength raw output) 5
        (initialNPOracleState inputLength
          (balancedValidationMapOutput inputLength raw output)) =
      some (balancedValidationAllLengthInput inputLength raw output) := by
  let outputCode :=
    encodeBalancedList
      (balancedValidationMapOutputs inputLength raw output)
  let context := balancedValidationMapContext raw
  let maximumBits :=
    balancedValidationAllLengthPrepareBits inputLength raw output
  have hbits :
      ∀ value ∈
          [ Nat.pair outputCode context
          , outputCode
          , context
          , Nat.pair outputCode context
          , balancedValidationAllLengthInput inputLength raw output
          ],
        natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact bitLength_le_foldr_max_of_mem hvalue
  have houtputCode : natBitLength outputCode ≤ maximumBits :=
    hbits outputCode (by simp)
  have hcontext : natBitLength context ≤ maximumBits :=
    hbits context (by simp)
  have htail :
      natBitLength (Nat.pair outputCode context) ≤ maximumBits :=
    hbits (Nat.pair outputCode context) (by simp)
  have houtput :
      natBitLength
          (balancedValidationAllLengthInput inputLength raw output) ≤
        maximumBits :=
    hbits (balancedValidationAllLengthInput inputLength raw output)
      (by simp)
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := balancedValidationAllLengthPrepareProgram)
    (maximumBits := maximumBits) (fuel := 4)
    (pc := 0) (source := 0) (destination := 2) (next := 1)
    (value := outputCode) (by rfl) rfl
    (by simp [initialNPOracleState, balancedValidationMapOutput,
      outputCode]) houtputCode]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := balancedValidationAllLengthPrepareProgram)
    (maximumBits := maximumBits) (fuel := 3)
    (pc := 1) (source := 0) (destination := 3) (next := 2)
    (value := context) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, balancedValidationMapOutput,
      outputCode, context]) hcontext]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (program := balancedValidationAllLengthPrepareProgram)
    (maximumBits := maximumBits) (fuel := 2)
    (pc := 2) (left := 2) (right := 3) (destination := 4) (next := 3)
    (value := Nat.pair outputCode context) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump]) htail]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (program := balancedValidationAllLengthPrepareProgram)
    (maximumBits := maximumBits) (fuel := 1)
    (pc := 3) (left := 2) (right := 4) (destination := 0) (next := 4)
    (value := balancedValidationAllLengthInput inputLength raw output)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, balancedValidationAllLengthInput,
      outputCode, context]) houtput]
  exact run_halt_instruction
    (program := balancedValidationAllLengthPrepareProgram)
    (maximumBits := maximumBits) (fuel := 0)
    (pc := 4) (outputRegister := 0)
    (value := balancedValidationAllLengthInput inputLength raw output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

def balancedValidationAllLengthOutput
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  let outputs := balancedValidationMapOutputs inputLength raw output
  Nat.pair outputs.length
    (Nat.pair (encodeBalancedList outputs)
      (balancedValidationMapContext raw))

def balancedValidationAllLengthProgram : NPOracleProgram :=
  linkPrograms balancedValidationAllLengthPrepareProgram <|
    preserveRightProgram balancedLengthProgram

@[simp] theorem balancedValidationAllLengthProgram_oracleFree :
    OracleFree balancedValidationAllLengthProgram := by
  exact oracleFree_linkPrograms
    balancedValidationAllLengthPrepareProgram_oracleFree <|
      preserveRightProgram_oracleFree balancedLengthProgram
        balancedLengthProgram_oracleFree

def balancedValidationAllLengthFuel
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  let outputs := balancedValidationMapOutputs inputLength raw output
  linkFuel (preserveRightProgram balancedLengthProgram) 5 <|
    preserveRightFuel (balancedLengthFuel outputs)

def balancedValidationAllLengthBits
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  let outputs := balancedValidationMapOutputs inputLength raw output
  let outputCode := encodeBalancedList outputs
  let context := balancedValidationMapContext raw
  max 1 <| max (natBitLength inputLength) <|
    max (balancedValidationAllLengthPrepareBits
      inputLength raw output) <|
      preserveRightBits (balancedLengthBits inputLength outputs)
        outputCode (Nat.pair outputCode context) outputs.length

theorem run_balancedValidationAllLengthProgram
    (inputLength raw : ℕ) (output : ℕ → ℕ) :
    runNPOracleProgram balancedValidationAllLengthProgram
        (balancedValidationAllLengthBits inputLength raw output)
        (balancedValidationAllLengthFuel inputLength raw output)
        (initialNPOracleState inputLength
          (balancedValidationMapOutput inputLength raw output)) =
      some (balancedValidationAllLengthOutput inputLength raw output) := by
  let outputs := balancedValidationMapOutputs inputLength raw output
  let outputCode := encodeBalancedList outputs
  let context := balancedValidationMapContext raw
  let maximumBits :=
    balancedValidationAllLengthBits inputLength raw output
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hlength : natBitLength inputLength ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hprepareBits :
      balancedValidationAllLengthPrepareBits inputLength raw output ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlengthBits :
      preserveRightBits (balancedLengthBits inputLength outputs)
          outputCode (Nat.pair outputCode context) outputs.length ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hprepare :=
    run_bits_mono
      (run_balancedValidationAllLengthPrepareProgram
        inputLength raw output)
      hprepareBits
  have hlengthSource :=
    run_balancedLengthProgram inputLength outputs
  have hlengthRun :
      runNPOracleProgram (preserveRightProgram balancedLengthProgram)
          maximumBits (preserveRightFuel (balancedLengthFuel outputs))
          (initialNPOracleState inputLength
            (balancedValidationAllLengthInput inputLength raw output)) =
        some (balancedValidationAllLengthOutput inputLength raw output) := by
    have hrun :=
      run_preserveRightProgram balancedLengthProgram inputLength
        (balancedLengthBits inputLength outputs)
        (balancedLengthFuel outputs)
        outputCode (Nat.pair outputCode context) outputs.length
        hlengthSource
    simpa [balancedValidationAllLengthInput,
      balancedValidationAllLengthOutput, outputs, outputCode, context]
      using run_bits_mono hrun hlengthBits
  have hrun :=
    run_linkPrograms hpositive hlength hprepare hlengthRun
  simpa [balancedValidationAllLengthProgram,
    balancedValidationAllLengthFuel] using hrun

def balancedValidationAllCountInput
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  let outputs := balancedValidationMapOutputs inputLength raw output
  Nat.pair
    (Nat.pair outputs.length (balancedValidationMapContext raw))
    (encodeBalancedList outputs)

def balancedValidationAllCountLoweringProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 2 5 6 5
  , .pair 6 4 0 6
  , .halt 0
  ]

@[simp] private theorem
    balancedValidationAllCountLoweringProgram_oracleFree :
    OracleFree balancedValidationAllCountLoweringProgram := by
  rfl

private def balancedValidationAllCountLoweringBits
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  let outputs := balancedValidationMapOutputs inputLength raw output
  let outputCode := encodeBalancedList outputs
  let context := balancedValidationMapContext raw
  [ balancedValidationAllLengthOutput inputLength raw output
  , outputs.length
  , Nat.pair outputCode context
  , outputCode
  , context
  , Nat.pair outputs.length context
  , balancedValidationAllCountInput inputLength raw output
  ].map natBitLength |>.foldr max 1

private theorem run_balancedValidationAllCountLoweringProgram
    (inputLength raw : ℕ) (output : ℕ → ℕ) :
    runNPOracleProgram balancedValidationAllCountLoweringProgram
        (balancedValidationAllCountLoweringBits inputLength raw output) 7
        (initialNPOracleState inputLength
          (balancedValidationAllLengthOutput inputLength raw output)) =
      some (balancedValidationAllCountInput inputLength raw output) := by
  let outputs := balancedValidationMapOutputs inputLength raw output
  let outputCode := encodeBalancedList outputs
  let context := balancedValidationMapContext raw
  let maximumBits :=
    balancedValidationAllCountLoweringBits inputLength raw output
  have hbits :
      ∀ value ∈
          [ balancedValidationAllLengthOutput inputLength raw output
          , outputs.length
          , Nat.pair outputCode context
          , outputCode
          , context
          , Nat.pair outputs.length context
          , balancedValidationAllCountInput inputLength raw output
          ],
        natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact bitLength_le_foldr_max_of_mem hvalue
  have hlength := hbits outputs.length (by simp)
  have htail := hbits (Nat.pair outputCode context) (by simp)
  have houtputCode := hbits outputCode (by simp)
  have hcontext := hbits context (by simp)
  have hcountContext :=
    hbits (Nat.pair outputs.length context) (by simp)
  have houtput :=
    hbits (balancedValidationAllCountInput inputLength raw output)
      (by simp)
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := balancedValidationAllCountLoweringProgram)
    (maximumBits := maximumBits) (fuel := 6)
    (pc := 0) (source := 0) (destination := 2) (next := 1)
    (value := outputs.length) (by rfl) rfl
    (by simp [initialNPOracleState,
      balancedValidationAllLengthOutput, outputs])
    hlength]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := balancedValidationAllCountLoweringProgram)
    (maximumBits := maximumBits) (fuel := 5)
    (pc := 1) (source := 0) (destination := 3) (next := 2)
    (value := Nat.pair outputCode context) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, balancedValidationAllLengthOutput,
      outputs, outputCode, context]) htail]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := balancedValidationAllCountLoweringProgram)
    (maximumBits := maximumBits) (fuel := 4)
    (pc := 2) (source := 3) (destination := 4) (next := 3)
    (value := outputCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtputCode]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := balancedValidationAllCountLoweringProgram)
    (maximumBits := maximumBits) (fuel := 3)
    (pc := 3) (source := 3) (destination := 5) (next := 4)
    (value := context) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcontext]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (program := balancedValidationAllCountLoweringProgram)
    (maximumBits := maximumBits) (fuel := 2)
    (pc := 4) (left := 2) (right := 5) (destination := 6) (next := 5)
    (value := Nat.pair outputs.length context)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcountContext]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (program := balancedValidationAllCountLoweringProgram)
    (maximumBits := maximumBits) (fuel := 1)
    (pc := 5) (left := 6) (right := 4) (destination := 0) (next := 6)
    (value := balancedValidationAllCountInput inputLength raw output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      balancedValidationAllCountInput, outputs, outputCode, context])
    houtput]
  exact run_halt_instruction
    (program := balancedValidationAllCountLoweringProgram)
    (maximumBits := maximumBits) (fuel := 0)
    (pc := 6) (outputRegister := 0)
    (value := balancedValidationAllCountInput inputLength raw output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

def balancedValidationAllCountOutput
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  let outputs := balancedValidationMapOutputs inputLength raw output
  Nat.pair (nonzeroAtomCount outputs)
    (Nat.pair outputs.length (balancedValidationMapContext raw))

def balancedValidationAllCountProgram : NPOracleProgram :=
  linkPrograms balancedValidationAllCountLoweringProgram
    balancedBoolCountProgram

@[simp] theorem balancedValidationAllCountProgram_oracleFree :
    OracleFree balancedValidationAllCountProgram := by
  exact oracleFree_linkPrograms
    balancedValidationAllCountLoweringProgram_oracleFree
    balancedBoolCountProgram_oracleFree

def balancedValidationAllCountFuel
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  let outputs := balancedValidationMapOutputs inputLength raw output
  linkFuel balancedBoolCountProgram 7
    (balancedNonzeroCountFuel outputs)

def balancedValidationAllCountBits
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  let outputs := balancedValidationMapOutputs inputLength raw output
  let context :=
    Nat.pair outputs.length (balancedValidationMapContext raw)
  max 1 <| max (natBitLength inputLength) <|
    max (balancedValidationAllCountLoweringBits
      inputLength raw output)
      (balancedNonzeroCountBits inputLength context outputs)

theorem run_balancedValidationAllCountProgram
    (inputLength raw : ℕ) (output : ℕ → ℕ) :
    runNPOracleProgram balancedValidationAllCountProgram
        (balancedValidationAllCountBits inputLength raw output)
        (balancedValidationAllCountFuel inputLength raw output)
        (initialNPOracleState inputLength
          (balancedValidationAllLengthOutput inputLength raw output)) =
      some (balancedValidationAllCountOutput inputLength raw output) := by
  let outputs := balancedValidationMapOutputs inputLength raw output
  let context :=
    Nat.pair outputs.length (balancedValidationMapContext raw)
  let maximumBits :=
    balancedValidationAllCountBits inputLength raw output
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hlength : natBitLength inputLength ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hloweringBits :
      balancedValidationAllCountLoweringBits inputLength raw output ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcountBits :
      balancedNonzeroCountBits inputLength context outputs ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlowering :=
    run_bits_mono
      (run_balancedValidationAllCountLoweringProgram
        inputLength raw output)
      hloweringBits
  have hcount :
      runNPOracleProgram balancedBoolCountProgram maximumBits
          (balancedNonzeroCountFuel outputs)
          (initialNPOracleState inputLength
            (balancedValidationAllCountInput inputLength raw output)) =
        some (balancedValidationAllCountOutput inputLength raw output) := by
    have hrun :=
      run_bits_mono
        (run_balancedNonzeroCountProgram inputLength context outputs)
        hcountBits
    simpa [balancedValidationAllCountInput,
      balancedValidationAllCountOutput, balancedNonzeroCountOutput,
      outputs, context] using hrun
  have hrun :=
    run_linkPrograms hpositive hlength hlowering hcount
  simpa [balancedValidationAllCountProgram,
    balancedValidationAllCountFuel] using hrun

def balancedValidationAllEqualityInput
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  let outputs := balancedValidationMapOutputs inputLength raw output
  Nat.pair
    (nativeNatEqInput (nonzeroAtomCount outputs) outputs.length)
    (balancedValidationMapContext raw)

def balancedValidationAllEqualityLoweringProgram :
    NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 2 4 6 5
  , .pair 6 5 0 6
  , .halt 0
  ]

@[simp] private theorem
    balancedValidationAllEqualityLoweringProgram_oracleFree :
    OracleFree balancedValidationAllEqualityLoweringProgram := by
  rfl

private def balancedValidationAllEqualityLoweringBits
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  let outputs := balancedValidationMapOutputs inputLength raw output
  let count := nonzeroAtomCount outputs
  let context := balancedValidationMapContext raw
  [ balancedValidationAllCountOutput inputLength raw output
  , count
  , Nat.pair outputs.length context
  , outputs.length
  , context
  , nativeNatEqInput count outputs.length
  , balancedValidationAllEqualityInput inputLength raw output
  ].map natBitLength |>.foldr max 1

private theorem run_balancedValidationAllEqualityLoweringProgram
    (inputLength raw : ℕ) (output : ℕ → ℕ) :
    runNPOracleProgram balancedValidationAllEqualityLoweringProgram
        (balancedValidationAllEqualityLoweringBits
          inputLength raw output) 7
        (initialNPOracleState inputLength
          (balancedValidationAllCountOutput inputLength raw output)) =
      some (balancedValidationAllEqualityInput inputLength raw output) := by
  let outputs := balancedValidationMapOutputs inputLength raw output
  let count := nonzeroAtomCount outputs
  let context := balancedValidationMapContext raw
  let equality := nativeNatEqInput count outputs.length
  let maximumBits :=
    balancedValidationAllEqualityLoweringBits inputLength raw output
  have hbits :
      ∀ value ∈
          [ balancedValidationAllCountOutput inputLength raw output
          , count
          , Nat.pair outputs.length context
          , outputs.length
          , context
          , equality
          , balancedValidationAllEqualityInput inputLength raw output
          ],
        natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact bitLength_le_foldr_max_of_mem hvalue
  have hcount := hbits count (by simp)
  have htail := hbits (Nat.pair outputs.length context) (by simp)
  have hlength := hbits outputs.length (by simp)
  have hcontext := hbits context (by simp)
  have hequality := hbits equality (by
    simp [equality])
  have houtput :=
    hbits (balancedValidationAllEqualityInput inputLength raw output)
      (by simp)
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := balancedValidationAllEqualityLoweringProgram)
    (maximumBits := maximumBits) (fuel := 6)
    (pc := 0) (source := 0) (destination := 2) (next := 1)
    (value := count) (by rfl) rfl
    (by simp [initialNPOracleState,
      balancedValidationAllCountOutput, outputs, count]) hcount]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := balancedValidationAllEqualityLoweringProgram)
    (maximumBits := maximumBits) (fuel := 5)
    (pc := 1) (source := 0) (destination := 3) (next := 2)
    (value := Nat.pair outputs.length context) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, balancedValidationAllCountOutput,
      outputs, count, context]) htail]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := balancedValidationAllEqualityLoweringProgram)
    (maximumBits := maximumBits) (fuel := 4)
    (pc := 2) (source := 3) (destination := 4) (next := 3)
    (value := outputs.length) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hlength]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := balancedValidationAllEqualityLoweringProgram)
    (maximumBits := maximumBits) (fuel := 3)
    (pc := 3) (source := 3) (destination := 5) (next := 4)
    (value := context) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcontext]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (program := balancedValidationAllEqualityLoweringProgram)
    (maximumBits := maximumBits) (fuel := 2)
    (pc := 4) (left := 2) (right := 4) (destination := 6) (next := 5)
    (value := equality) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      equality, nativeNatEqInput]) hequality]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (program := balancedValidationAllEqualityLoweringProgram)
    (maximumBits := maximumBits) (fuel := 1)
    (pc := 5) (left := 6) (right := 5) (destination := 0) (next := 6)
    (value := balancedValidationAllEqualityInput inputLength raw output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      balancedValidationAllEqualityInput, outputs, count, context,
      equality, nativeNatEqInput]) houtput]
  exact run_halt_instruction
    (program := balancedValidationAllEqualityLoweringProgram)
    (maximumBits := maximumBits) (fuel := 0)
    (pc := 6) (outputRegister := 0)
    (value := balancedValidationAllEqualityInput inputLength raw output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

def balancedValidationAllEqualityOutput
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  let outputs := balancedValidationMapOutputs inputLength raw output
  Nat.pair
    (nativeNatEqOutput (nonzeroAtomCount outputs) outputs.length)
    (balancedValidationMapContext raw)

def balancedValidationAllEqualityProgram : NPOracleProgram :=
  linkPrograms balancedValidationAllEqualityLoweringProgram <|
    preserveRightProgram nativeNatEqProgram

@[simp] theorem balancedValidationAllEqualityProgram_oracleFree :
    OracleFree balancedValidationAllEqualityProgram := by
  exact oracleFree_linkPrograms
    balancedValidationAllEqualityLoweringProgram_oracleFree <|
      preserveRightProgram_oracleFree nativeNatEqProgram
        nativeNatEqProgram_oracleFree

def balancedValidationAllEqualityFuel
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  let outputs := balancedValidationMapOutputs inputLength raw output
  linkFuel (preserveRightProgram nativeNatEqProgram) 7 <|
    preserveRightFuel
      (nativeNatEqFuel (nonzeroAtomCount outputs) outputs.length)

def balancedValidationAllEqualityBits
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  let outputs := balancedValidationMapOutputs inputLength raw output
  let count := nonzeroAtomCount outputs
  let context := balancedValidationMapContext raw
  let equality := nativeNatEqInput count outputs.length
  max 1 <| max (natBitLength inputLength) <|
    max (balancedValidationAllEqualityLoweringBits
      inputLength raw output)
      (preserveRightBits
        (nativeNatEqBits inputLength count outputs.length)
        equality context (nativeNatEqOutput count outputs.length))

theorem run_balancedValidationAllEqualityProgram
    (inputLength raw : ℕ) (output : ℕ → ℕ) :
    runNPOracleProgram balancedValidationAllEqualityProgram
        (balancedValidationAllEqualityBits inputLength raw output)
        (balancedValidationAllEqualityFuel inputLength raw output)
        (initialNPOracleState inputLength
          (balancedValidationAllCountOutput inputLength raw output)) =
      some
        (balancedValidationAllEqualityOutput inputLength raw output) := by
  let outputs := balancedValidationMapOutputs inputLength raw output
  let count := nonzeroAtomCount outputs
  let context := balancedValidationMapContext raw
  let equality := nativeNatEqInput count outputs.length
  let equalityOutput := nativeNatEqOutput count outputs.length
  let maximumBits :=
    balancedValidationAllEqualityBits inputLength raw output
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hlength : natBitLength inputLength ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hloweringBits :
      balancedValidationAllEqualityLoweringBits
          inputLength raw output ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hequalityBits :
      preserveRightBits
          (nativeNatEqBits inputLength count outputs.length)
          equality context equalityOutput ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlowering :=
    run_bits_mono
      (run_balancedValidationAllEqualityLoweringProgram
        inputLength raw output)
      hloweringBits
  have hequality :
      runNPOracleProgram (preserveRightProgram nativeNatEqProgram)
          maximumBits
          (preserveRightFuel
            (nativeNatEqFuel count outputs.length))
          (initialNPOracleState inputLength
            (balancedValidationAllEqualityInput inputLength raw output)) =
        some
          (balancedValidationAllEqualityOutput inputLength raw output) := by
    have hrun :=
      run_preserveRightProgram nativeNatEqProgram inputLength
        (nativeNatEqBits inputLength count outputs.length)
        (nativeNatEqFuel count outputs.length)
        equality context equalityOutput
        (run_nativeNatEqProgram inputLength count outputs.length)
    simpa [balancedValidationAllEqualityInput,
      balancedValidationAllEqualityOutput, outputs, count, context,
      equality, equalityOutput] using
        run_bits_mono hrun hequalityBits
  have hrun :=
    run_linkPrograms hpositive hlength hlowering hequality
  simpa [balancedValidationAllEqualityProgram,
    balancedValidationAllEqualityFuel] using hrun

def balancedValidationAllAccepts
    (inputLength raw : ℕ) (output : ℕ → ℕ) : Prop :=
  let outputs := balancedValidationMapOutputs inputLength raw output
  balancedValidationMapFlag raw ≠ 0 ∧
    nonzeroAtomCount outputs = outputs.length

private instance (inputLength raw : ℕ) (output : ℕ → ℕ) :
    Decidable (balancedValidationAllAccepts inputLength raw output) := by
  unfold balancedValidationAllAccepts
  infer_instance

def balancedValidationAllOutput
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  if balancedValidationAllAccepts inputLength raw output then
    Nat.pair 1 raw
  else
    0

def balancedValidationAllGateProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .branchZero 2 8 2
  , .unpairRight 0 3 3
  , .unpairLeft 3 4 4
  , .branchZero 4 8 5
  , .unpairRight 3 6 6
  , .set 7 1 7
  , .pair 7 6 0 9
  , .set 0 0 9
  , .halt 0
  ]

@[simp] private theorem balancedValidationAllGateProgram_oracleFree :
    OracleFree balancedValidationAllGateProgram := by
  rfl

def balancedValidationAllGateFuel : ℕ := 9

private def balancedValidationAllGateBits
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  let outputs := balancedValidationMapOutputs inputLength raw output
  let equality :=
    nativeNatEqOutput (nonzeroAtomCount outputs) outputs.length
  let flag := balancedValidationMapFlag raw
  let context := balancedValidationMapContext raw
  [ balancedValidationAllEqualityOutput inputLength raw output
  , equality
  , context
  , flag
  , raw
  , 0
  , 1
  , Nat.pair 1 raw
  , balancedValidationAllOutput inputLength raw output
  ].map natBitLength |>.foldr max 1

private theorem run_balancedValidationAllGateProgram
    (inputLength raw : ℕ) (output : ℕ → ℕ) :
    runNPOracleProgram balancedValidationAllGateProgram
        (balancedValidationAllGateBits inputLength raw output)
        balancedValidationAllGateFuel
        (initialNPOracleState inputLength
          (balancedValidationAllEqualityOutput inputLength raw output)) =
      some (balancedValidationAllOutput inputLength raw output) := by
  let outputs := balancedValidationMapOutputs inputLength raw output
  let count := nonzeroAtomCount outputs
  let equality := nativeNatEqOutput count outputs.length
  let flag := balancedValidationMapFlag raw
  let context := balancedValidationMapContext raw
  let accepted := Nat.pair 1 raw
  let maximumBits :=
    balancedValidationAllGateBits inputLength raw output
  have hbits :
      ∀ value ∈
          [ balancedValidationAllEqualityOutput inputLength raw output
          , equality
          , context
          , flag
          , raw
          , 0
          , 1
          , accepted
          , balancedValidationAllOutput inputLength raw output
          ],
        natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact bitLength_le_foldr_max_of_mem hvalue
  have hequality := hbits equality (by simp)
  have hcontext := hbits context (by simp)
  have hflag := hbits flag (by simp)
  have hraw := hbits raw (by simp)
  have hzero := hbits 0 (by simp)
  have hone := hbits 1 (by simp)
  have haccepted := hbits accepted (by simp [accepted])
  have houtput :=
    hbits (balancedValidationAllOutput inputLength raw output) (by simp)
  rw [show balancedValidationAllGateFuel = 8 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (program := balancedValidationAllGateProgram)
    (maximumBits := maximumBits) (fuel := 8)
    (pc := 0) (source := 0) (destination := 2) (next := 1)
    (value := equality) (by rfl) rfl
    (by simp [initialNPOracleState,
      balancedValidationAllEqualityOutput, outputs, count, equality])
    hequality]
  rw [show 8 = 7 + 1 by omega]
  rw [run_branchZero_instruction
    (program := balancedValidationAllGateProgram)
    (maximumBits := maximumBits) (fuel := 7)
    (pc := 1) (register := 2) (zeroTarget := 8)
    (nonzeroTarget := 2) (by rfl) rfl]
  by_cases hequal : count = outputs.length
  · have hequalityOne : equality = 1 := by
      simp [equality, nativeNatEqOutput, hequal]
    rw [show
      (((initialNPOracleState inputLength
        (balancedValidationAllEqualityOutput inputLength raw output)).write
          2 equality).jump 1).registers 2 = 1 by
        simp [NPOracleState.write, NPOracleState.jump, hequalityOne]]
    rw [if_neg (by omega)]
    rw [show 7 = 6 + 1 by omega]
    rw [run_unpairRight_instruction
      (program := balancedValidationAllGateProgram)
      (maximumBits := maximumBits) (fuel := 6)
      (pc := 2) (source := 0) (destination := 3) (next := 3)
      (value := context) (by rfl) rfl
      (by simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, balancedValidationAllEqualityOutput,
        outputs, count, equality, context]) hcontext]
    rw [show 6 = 5 + 1 by omega]
    rw [run_unpairLeft_instruction
      (program := balancedValidationAllGateProgram)
      (maximumBits := maximumBits) (fuel := 5)
      (pc := 3) (source := 3) (destination := 4) (next := 4)
      (value := flag) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump,
        context, balancedValidationMapContext, flag]) hflag]
    rw [show 5 = 4 + 1 by omega]
    rw [run_branchZero_instruction
      (program := balancedValidationAllGateProgram)
      (maximumBits := maximumBits) (fuel := 4)
      (pc := 4) (register := 4) (zeroTarget := 8)
      (nonzeroTarget := 5) (by rfl) rfl]
    by_cases hflagZero : flag = 0
    · rw [show
        ((((((((initialNPOracleState inputLength
          (balancedValidationAllEqualityOutput inputLength raw output)).write
            2 equality).jump 1).jump 2).write 3 context).jump 3).write
              4 flag).jump 4).registers 4 = 0 by
          simp [NPOracleState.write, NPOracleState.jump, hflagZero]]
      rw [if_pos rfl]
      rw [show 4 = 3 + 1 by omega]
      rw [run_set_instruction
        (program := balancedValidationAllGateProgram)
        (maximumBits := maximumBits) (fuel := 3)
        (pc := 8) (register := 0) (value := 0) (next := 9)
        (by rfl) rfl hzero]
      have hrejected :
          balancedValidationAllOutput inputLength raw output = 0 := by
        simp [balancedValidationAllOutput,
          balancedValidationAllAccepts, flag, hflagZero]
      rw [hrejected]
      exact run_halt_instruction
        (program := balancedValidationAllGateProgram)
        (maximumBits := maximumBits) (fuel := 2)
        (pc := 9) (outputRegister := 0) (value := 0)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hzero
    · rw [show
        ((((((((initialNPOracleState inputLength
          (balancedValidationAllEqualityOutput inputLength raw output)).write
            2 equality).jump 1).jump 2).write 3 context).jump 3).write
              4 flag).jump 4).registers 4 = flag by
          simp [NPOracleState.write, NPOracleState.jump]]
      rw [if_neg hflagZero]
      rw [show 4 = 3 + 1 by omega]
      rw [run_unpairRight_instruction
        (program := balancedValidationAllGateProgram)
        (maximumBits := maximumBits) (fuel := 3)
        (pc := 5) (source := 3) (destination := 6) (next := 6)
        (value := raw) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump,
          context, balancedValidationMapContext]) hraw]
      rw [show 3 = 2 + 1 by omega]
      rw [run_set_instruction
        (program := balancedValidationAllGateProgram)
        (maximumBits := maximumBits) (fuel := 2)
        (pc := 6) (register := 7) (value := 1) (next := 7)
        (by rfl) rfl hone]
      rw [show 2 = 1 + 1 by omega]
      have haccepts :
          balancedValidationAllOutput inputLength raw output = accepted := by
        simp [balancedValidationAllOutput,
          balancedValidationAllAccepts, outputs, count, flag,
          hflagZero, hequal, accepted]
      rw [run_pair_instruction
        (program := balancedValidationAllGateProgram)
        (maximumBits := maximumBits) (fuel := 1)
        (pc := 7) (left := 7) (right := 6) (destination := 0) (next := 9)
        (value := accepted) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, accepted])
        haccepted]
      rw [haccepts]
      exact run_halt_instruction
        (program := balancedValidationAllGateProgram)
        (maximumBits := maximumBits) (fuel := 0)
        (pc := 9) (outputRegister := 0) (value := accepted)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) haccepted
  · have hequalityZero : equality = 0 := by
      simp [equality, nativeNatEqOutput, hequal]
    rw [show
      (((initialNPOracleState inputLength
        (balancedValidationAllEqualityOutput inputLength raw output)).write
          2 equality).jump 1).registers 2 = 0 by
        simp [NPOracleState.write, NPOracleState.jump, hequalityZero]]
    rw [if_pos rfl]
    rw [show 7 = 6 + 1 by omega]
    rw [run_set_instruction
      (program := balancedValidationAllGateProgram)
      (maximumBits := maximumBits) (fuel := 6)
      (pc := 8) (register := 0) (value := 0) (next := 9)
      (by rfl) rfl hzero]
    have hrejected :
        balancedValidationAllOutput inputLength raw output = 0 := by
      simp [balancedValidationAllOutput,
        balancedValidationAllAccepts, outputs, count, hequal]
    rw [hrejected]
    exact run_halt_instruction
      (program := balancedValidationAllGateProgram)
      (maximumBits := maximumBits) (fuel := 5)
      (pc := 9) (outputRegister := 0) (value := 0)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hzero

def balancedValidationAllCheckedTailProgram : NPOracleProgram :=
  linkPrograms balancedValidationAllCountProgram <|
    linkPrograms balancedValidationAllEqualityProgram
      balancedValidationAllGateProgram

def balancedValidationAllProgram
    (callee : NPOracleProgram) : NPOracleProgram :=
  linkPrograms (balancedValidationMapProgram callee) <|
    linkPrograms balancedValidationAllLengthProgram
      balancedValidationAllCheckedTailProgram

@[simp] theorem balancedValidationAllProgram_oracleFree
    (callee : NPOracleProgram) (hcallee : OracleFree callee) :
    OracleFree (balancedValidationAllProgram callee) := by
  exact oracleFree_linkPrograms
    (balancedValidationMapProgram_oracleFree callee hcallee) <|
      oracleFree_linkPrograms
        balancedValidationAllLengthProgram_oracleFree <|
          oracleFree_linkPrograms
            balancedValidationAllCountProgram_oracleFree <|
              oracleFree_linkPrograms
                balancedValidationAllEqualityProgram_oracleFree
                balancedValidationAllGateProgram_oracleFree

def balancedValidationAllFuel
    (callee : NPOracleProgram) (calleeFuel : ℕ → ℕ)
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  linkFuel
    (linkPrograms balancedValidationAllLengthProgram <|
      linkPrograms balancedValidationAllCountProgram <|
        linkPrograms balancedValidationAllEqualityProgram
          balancedValidationAllGateProgram)
    (balancedValidationMapFuel callee calleeFuel inputLength raw) <|
      linkFuel
        (linkPrograms balancedValidationAllCountProgram <|
          linkPrograms balancedValidationAllEqualityProgram
            balancedValidationAllGateProgram)
        (balancedValidationAllLengthFuel inputLength raw output) <|
          linkFuel
            (linkPrograms balancedValidationAllEqualityProgram
              balancedValidationAllGateProgram)
            (balancedValidationAllCountFuel inputLength raw output) <|
              linkFuel balancedValidationAllGateProgram
                (balancedValidationAllEqualityFuel inputLength raw output)
                balancedValidationAllGateFuel

def balancedValidationAllBits
    (calleeBits output : ℕ → ℕ)
    (inputLength raw : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (balancedValidationMapBits
      calleeBits output inputLength raw) <|
      max (balancedValidationAllLengthBits inputLength raw output) <|
        max (balancedValidationAllCountBits inputLength raw output) <|
          max (balancedValidationAllEqualityBits inputLength raw output)
            (balancedValidationAllGateBits inputLength raw output)

theorem run_balancedValidationAllProgram
    (callee : NPOracleProgram)
    (calleeBits calleeFuel output : ℕ → ℕ)
    (inputLength raw : ℕ)
    (hexec :
      ∀ request,
        request ∈ balancedValidationMapRequests inputLength raw →
          runNPOracleProgram callee (calleeBits request)
              (calleeFuel request)
              (initialNPOracleState
                (Nat.unpair request).1 (Nat.unpair request).2) =
            some (output request)) :
    runNPOracleProgram (balancedValidationAllProgram callee)
        (balancedValidationAllBits calleeBits output inputLength raw)
        (balancedValidationAllFuel callee calleeFuel
          inputLength raw output)
        (initialNPOracleState inputLength raw) =
      some (balancedValidationAllOutput inputLength raw output) := by
  let maximumBits :=
    balancedValidationAllBits calleeBits output inputLength raw
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hlength : natBitLength inputLength ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hmapBits :
      balancedValidationMapBits calleeBits output inputLength raw ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlengthBits :
      balancedValidationAllLengthBits inputLength raw output ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcountBits :
      balancedValidationAllCountBits inputLength raw output ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hequalityBits :
      balancedValidationAllEqualityBits inputLength raw output ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hgateBits :
      balancedValidationAllGateBits inputLength raw output ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hmap :=
    run_bits_mono
      (run_balancedValidationMapProgram callee
        calleeBits calleeFuel output inputLength raw hexec)
      hmapBits
  have hlengthRun :=
    run_bits_mono
      (run_balancedValidationAllLengthProgram inputLength raw output)
      hlengthBits
  have hcount :=
    run_bits_mono
      (run_balancedValidationAllCountProgram inputLength raw output)
      hcountBits
  have hequality :=
    run_bits_mono
      (run_balancedValidationAllEqualityProgram inputLength raw output)
      hequalityBits
  have hgate :=
    run_bits_mono
      (run_balancedValidationAllGateProgram inputLength raw output)
      hgateBits
  have hequalityGate :=
    run_linkPrograms hpositive hlength hequality hgate
  have hcountTail :=
    run_linkPrograms hpositive hlength hcount hequalityGate
  have hlengthTail :=
    run_linkPrograms hpositive hlength hlengthRun hcountTail
  have hrun :=
    run_linkPrograms hpositive hlength hmap hlengthTail
  simpa [balancedValidationAllProgram,
    balancedValidationAllCheckedTailProgram,
    balancedValidationAllFuel] using hrun

def balancedValidationSummaryData
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  let outputs := balancedValidationMapOutputs inputLength raw output
  Nat.pair (encodeBalancedList outputs)
    (Nat.pair outputs.length raw)

private def balancedValidationSummaryPrepareOutput
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  Nat.pair
    (balancedValidationAllLengthOutput inputLength raw output)
    (balancedValidationSummaryData inputLength raw output)

def balancedValidationSummaryPrepareProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairRight 5 6 5
  , .pair 2 6 7 6
  , .pair 4 7 8 7
  , .pair 0 8 0 8
  , .halt 0
  ]

@[simp] private theorem
    balancedValidationSummaryPrepareProgram_oracleFree :
    OracleFree balancedValidationSummaryPrepareProgram := by
  rfl

private def balancedValidationSummaryPrepareBits
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  let outputs := balancedValidationMapOutputs inputLength raw output
  let outputCode := encodeBalancedList outputs
  let context := balancedValidationMapContext raw
  [ balancedValidationAllLengthOutput inputLength raw output
  , outputs.length
  , Nat.pair outputCode context
  , outputCode
  , context
  , raw
  , Nat.pair outputs.length raw
  , balancedValidationSummaryData inputLength raw output
  , balancedValidationSummaryPrepareOutput inputLength raw output
  ].map natBitLength |>.foldr max 1

private theorem run_balancedValidationSummaryPrepareProgram
    (inputLength raw : ℕ) (output : ℕ → ℕ) :
    runNPOracleProgram balancedValidationSummaryPrepareProgram
        (balancedValidationSummaryPrepareBits inputLength raw output) 9
        (initialNPOracleState inputLength
          (balancedValidationAllLengthOutput inputLength raw output)) =
      some
        (balancedValidationSummaryPrepareOutput
          inputLength raw output) := by
  let outputs := balancedValidationMapOutputs inputLength raw output
  let outputCode := encodeBalancedList outputs
  let context := balancedValidationMapContext raw
  let lengthRaw := Nat.pair outputs.length raw
  let summary := balancedValidationSummaryData inputLength raw output
  let prepared :=
    balancedValidationSummaryPrepareOutput inputLength raw output
  let maximumBits :=
    balancedValidationSummaryPrepareBits inputLength raw output
  have hbits :
      ∀ value ∈
          [ balancedValidationAllLengthOutput inputLength raw output
          , outputs.length
          , Nat.pair outputCode context
          , outputCode
          , context
          , raw
          , lengthRaw
          , summary
          , prepared
          ],
        natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact bitLength_le_foldr_max_of_mem hvalue
  have hlength := hbits outputs.length (by simp)
  have htail := hbits (Nat.pair outputCode context) (by simp)
  have houtputCode := hbits outputCode (by simp)
  have hcontext := hbits context (by simp)
  have hraw := hbits raw (by simp)
  have hlengthRaw := hbits lengthRaw (by simp)
  have hsummary := hbits summary (by simp)
  have hprepared := hbits prepared (by simp)
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction
    (value := outputs.length) (by rfl) rfl
    (by simp [initialNPOracleState,
      balancedValidationAllLengthOutput, outputs])
    hlength]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair outputCode context) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, balancedValidationAllLengthOutput,
      outputs, outputCode, context])
    htail]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction
    (value := outputCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtputCode]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := context) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hcontext]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := raw) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      context, balancedValidationMapContext])
    hraw]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction
    (value := lengthRaw) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, lengthRaw])
    hlengthRaw]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := summary) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      summary, balancedValidationSummaryData, outputs, outputCode,
      lengthRaw])
    hsummary]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := prepared) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, prepared,
      balancedValidationSummaryPrepareOutput, summary])
    hprepared]
  exact run_halt_instruction (fuel := 0) (value := prepared)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hprepared

def balancedValidationAllCheckedTailFuel
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  linkFuel
    (linkPrograms balancedValidationAllEqualityProgram
      balancedValidationAllGateProgram)
    (balancedValidationAllCountFuel inputLength raw output) <|
      linkFuel balancedValidationAllGateProgram
        (balancedValidationAllEqualityFuel inputLength raw output)
        balancedValidationAllGateFuel

private def balancedValidationAllCheckedTailBits
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (balancedValidationAllCountBits inputLength raw output) <|
      max (balancedValidationAllEqualityBits inputLength raw output)
        (balancedValidationAllGateBits inputLength raw output)

private theorem run_balancedValidationAllCheckedTailProgram
    (inputLength raw : ℕ) (output : ℕ → ℕ) :
    runNPOracleProgram balancedValidationAllCheckedTailProgram
        (balancedValidationAllCheckedTailBits inputLength raw output)
        (balancedValidationAllCheckedTailFuel inputLength raw output)
        (initialNPOracleState inputLength
          (balancedValidationAllLengthOutput inputLength raw output)) =
      some (balancedValidationAllOutput inputLength raw output) := by
  let maximumBits :=
    balancedValidationAllCheckedTailBits inputLength raw output
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hlength : natBitLength inputLength ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hcountBits :
      balancedValidationAllCountBits inputLength raw output ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hequalityBits :
      balancedValidationAllEqualityBits inputLength raw output ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hgateBits :
      balancedValidationAllGateBits inputLength raw output ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcount :=
    run_bits_mono
      (run_balancedValidationAllCountProgram inputLength raw output)
      hcountBits
  have hequality :=
    run_bits_mono
      (run_balancedValidationAllEqualityProgram inputLength raw output)
      hequalityBits
  have hgate :=
    run_bits_mono
      (run_balancedValidationAllGateProgram inputLength raw output)
      hgateBits
  have hequalityGate :=
    run_linkPrograms hpositive hlength hequality hgate
  have hrun :=
    run_linkPrograms hpositive hlength hcount hequalityGate
  simpa [balancedValidationAllCheckedTailProgram,
    balancedValidationAllCheckedTailFuel] using hrun

private def balancedValidationSummaryCheckedOutput
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  Nat.pair (balancedValidationAllOutput inputLength raw output)
    (balancedValidationSummaryData inputLength raw output)

def balancedValidationSummaryCheckedProgram : NPOracleProgram :=
  preserveRightProgram balancedValidationAllCheckedTailProgram

@[simp] private theorem
    balancedValidationSummaryCheckedProgram_oracleFree :
    OracleFree balancedValidationSummaryCheckedProgram :=
  preserveRightProgram_oracleFree
    balancedValidationAllCheckedTailProgram <| by
      exact oracleFree_linkPrograms
        balancedValidationAllCountProgram_oracleFree <|
          oracleFree_linkPrograms
            balancedValidationAllEqualityProgram_oracleFree
            balancedValidationAllGateProgram_oracleFree

def balancedValidationSummaryCheckedFuel
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  preserveRightFuel <|
    balancedValidationAllCheckedTailFuel inputLength raw output

private def balancedValidationSummaryCheckedBits
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  preserveRightBits
    (balancedValidationAllCheckedTailBits inputLength raw output)
    (balancedValidationAllLengthOutput inputLength raw output)
    (balancedValidationSummaryData inputLength raw output)
    (balancedValidationAllOutput inputLength raw output)

private theorem run_balancedValidationSummaryCheckedProgram
    (inputLength raw : ℕ) (output : ℕ → ℕ) :
    runNPOracleProgram balancedValidationSummaryCheckedProgram
        (balancedValidationSummaryCheckedBits inputLength raw output)
        (balancedValidationSummaryCheckedFuel inputLength raw output)
        (initialNPOracleState inputLength
          (balancedValidationSummaryPrepareOutput
            inputLength raw output)) =
      some
        (balancedValidationSummaryCheckedOutput
          inputLength raw output) := by
  exact run_preserveRightProgram
    balancedValidationAllCheckedTailProgram inputLength
    (balancedValidationAllCheckedTailBits inputLength raw output)
    (balancedValidationAllCheckedTailFuel inputLength raw output)
    (balancedValidationAllLengthOutput inputLength raw output)
    (balancedValidationSummaryData inputLength raw output)
    (balancedValidationAllOutput inputLength raw output)
    (run_balancedValidationAllCheckedTailProgram
      inputLength raw output)

def balancedValidationSummaryOutput
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  if balancedValidationAllOutput inputLength raw output = 0 then
    0
  else
    Nat.pair 1
      (balancedValidationSummaryData inputLength raw output)

def balancedValidationSummaryGateProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .branchZero 2 6 2
  , .unpairRight 0 3 3
  , .set 4 1 4
  , .pair 4 3 0 5
  , .halt 0
  , .set 0 0 7
  , .halt 0
  ]

@[simp] private theorem balancedValidationSummaryGateProgram_oracleFree :
    OracleFree balancedValidationSummaryGateProgram := by
  rfl

private def balancedValidationSummaryGateBits
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  [ balancedValidationSummaryCheckedOutput inputLength raw output
  , balancedValidationAllOutput inputLength raw output
  , balancedValidationSummaryData inputLength raw output
  , balancedValidationSummaryOutput inputLength raw output
  , 0
  , 1
  , Nat.pair 1 (balancedValidationSummaryData inputLength raw output)
  ].map natBitLength |>.foldr max 1

private theorem run_balancedValidationSummaryGateProgram
    (inputLength raw : ℕ) (output : ℕ → ℕ) :
    runNPOracleProgram balancedValidationSummaryGateProgram
        (balancedValidationSummaryGateBits inputLength raw output) 6
        (initialNPOracleState inputLength
          (balancedValidationSummaryCheckedOutput
            inputLength raw output)) =
      some (balancedValidationSummaryOutput inputLength raw output) := by
  let allOutput := balancedValidationAllOutput inputLength raw output
  let summary := balancedValidationSummaryData inputLength raw output
  let checked :=
    balancedValidationSummaryCheckedOutput inputLength raw output
  let result := balancedValidationSummaryOutput inputLength raw output
  let accepted := Nat.pair 1 summary
  let maximumBits :=
    balancedValidationSummaryGateBits inputLength raw output
  have hbits :
      ∀ value ∈ [checked, allOutput, summary, result, 0, 1, accepted],
        natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact bitLength_le_foldr_max_of_mem hvalue
  have hall := hbits allOutput (by simp)
  have hsummary := hbits summary (by simp)
  have hzero := hbits 0 (by simp)
  have hone := hbits 1 (by simp)
  have haccepted := hbits accepted (by simp [accepted])
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction
    (value := allOutput) (by rfl) rfl
    (by simp [initialNPOracleState,
      balancedValidationSummaryCheckedOutput, allOutput])
    hall]
  rw [show 5 = 4 + 1 by omega]
  rw [run_branchZero_instruction (by rfl) rfl]
  by_cases hrejected : allOutput = 0
  · rw [show
      (((initialNPOracleState inputLength checked).write
        2 allOutput).jump 1).registers 2 = 0 by
          simp [NPOracleState.write, NPOracleState.jump, hrejected]]
    rw [if_pos rfl]
    rw [show 4 = 3 + 1 by omega]
    rw [run_set_instruction (by rfl) rfl hzero]
    have hresult :
        balancedValidationSummaryOutput inputLength raw output = 0 := by
      simp [balancedValidationSummaryOutput, allOutput,
        hrejected]
    rw [hresult]
    exact run_halt_instruction (fuel := 2) (value := 0)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      hzero
  · rw [show
      (((initialNPOracleState inputLength checked).write
        2 allOutput).jump 1).registers 2 = allOutput by
          simp [NPOracleState.write, NPOracleState.jump]]
    rw [if_neg hrejected]
    rw [show 4 = 3 + 1 by omega]
    rw [run_unpairRight_instruction
      (value := summary) (by rfl) rfl
      (by simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, balancedValidationSummaryCheckedOutput,
        summary])
      hsummary]
    rw [show 3 = 2 + 1 by omega]
    rw [run_set_instruction (by rfl) rfl hone]
    rw [show 2 = 1 + 1 by omega]
    rw [run_pair_instruction (value := accepted)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, accepted])
      haccepted]
    have hresult :
        balancedValidationSummaryOutput inputLength raw output =
          accepted := by
      simp [balancedValidationSummaryOutput, allOutput,
        hrejected, summary, accepted]
    rw [hresult]
    exact run_halt_instruction (fuel := 0) (value := accepted)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      haccepted

def balancedValidationSummaryProgram
    (callee : NPOracleProgram) : NPOracleProgram :=
  linkPrograms (balancedValidationMapProgram callee) <|
    linkPrograms balancedValidationAllLengthProgram <|
      linkPrograms balancedValidationSummaryPrepareProgram <|
        linkPrograms balancedValidationSummaryCheckedProgram
          balancedValidationSummaryGateProgram

@[simp] theorem balancedValidationSummaryProgram_oracleFree
    (callee : NPOracleProgram) (hcallee : OracleFree callee) :
    OracleFree (balancedValidationSummaryProgram callee) :=
  oracleFree_linkPrograms
    (balancedValidationMapProgram_oracleFree callee hcallee) <|
      oracleFree_linkPrograms
        balancedValidationAllLengthProgram_oracleFree <|
          oracleFree_linkPrograms
            balancedValidationSummaryPrepareProgram_oracleFree <|
              oracleFree_linkPrograms
                balancedValidationSummaryCheckedProgram_oracleFree
                balancedValidationSummaryGateProgram_oracleFree

def balancedValidationSummaryFuel
    (callee : NPOracleProgram) (calleeFuel : ℕ → ℕ)
    (inputLength raw : ℕ) (output : ℕ → ℕ) : ℕ :=
  linkFuel
    (linkPrograms balancedValidationAllLengthProgram <|
      linkPrograms balancedValidationSummaryPrepareProgram <|
        linkPrograms balancedValidationSummaryCheckedProgram
          balancedValidationSummaryGateProgram)
    (balancedValidationMapFuel callee calleeFuel inputLength raw) <|
      linkFuel
        (linkPrograms balancedValidationSummaryPrepareProgram <|
          linkPrograms balancedValidationSummaryCheckedProgram
            balancedValidationSummaryGateProgram)
        (balancedValidationAllLengthFuel inputLength raw output) <|
          linkFuel
            (linkPrograms balancedValidationSummaryCheckedProgram
              balancedValidationSummaryGateProgram)
            9 <|
              linkFuel balancedValidationSummaryGateProgram
                (balancedValidationSummaryCheckedFuel
                  inputLength raw output)
                6

def balancedValidationSummaryBits
    (calleeBits output : ℕ → ℕ)
    (inputLength raw : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (balancedValidationMapBits
      calleeBits output inputLength raw) <|
      max (balancedValidationAllLengthBits inputLength raw output) <|
        max (balancedValidationSummaryPrepareBits
          inputLength raw output) <|
          max (balancedValidationSummaryCheckedBits
            inputLength raw output)
            (balancedValidationSummaryGateBits inputLength raw output)

theorem run_balancedValidationSummaryProgram
    (callee : NPOracleProgram)
    (calleeBits calleeFuel output : ℕ → ℕ)
    (inputLength raw : ℕ)
    (hexec :
      ∀ request,
        request ∈ balancedValidationMapRequests inputLength raw →
          runNPOracleProgram callee (calleeBits request)
              (calleeFuel request)
              (initialNPOracleState
                (Nat.unpair request).1 (Nat.unpair request).2) =
            some (output request)) :
    runNPOracleProgram (balancedValidationSummaryProgram callee)
        (balancedValidationSummaryBits
          calleeBits output inputLength raw)
        (balancedValidationSummaryFuel callee calleeFuel
          inputLength raw output)
        (initialNPOracleState inputLength raw) =
      some (balancedValidationSummaryOutput
        inputLength raw output) := by
  let maximumBits :=
    balancedValidationSummaryBits
      calleeBits output inputLength raw
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hlength : natBitLength inputLength ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hmapBits :
      balancedValidationMapBits calleeBits output inputLength raw ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlengthBits :
      balancedValidationAllLengthBits inputLength raw output ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hprepareBits :
      balancedValidationSummaryPrepareBits inputLength raw output ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcheckedBits :
      balancedValidationSummaryCheckedBits inputLength raw output ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hgateBits :
      balancedValidationSummaryGateBits inputLength raw output ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hmap :=
    run_bits_mono
      (run_balancedValidationMapProgram callee
        calleeBits calleeFuel output inputLength raw hexec)
      hmapBits
  have hlengthRun :=
    run_bits_mono
      (run_balancedValidationAllLengthProgram inputLength raw output)
      hlengthBits
  have hprepare :=
    run_bits_mono
      (run_balancedValidationSummaryPrepareProgram
        inputLength raw output)
      hprepareBits
  have hchecked :=
    run_bits_mono
      (run_balancedValidationSummaryCheckedProgram
        inputLength raw output)
      hcheckedBits
  have hgate :=
    run_bits_mono
      (run_balancedValidationSummaryGateProgram
        inputLength raw output)
      hgateBits
  have hcheckedGate :=
    run_linkPrograms hpositive hlength hchecked hgate
  have hprepareTail :=
    run_linkPrograms hpositive hlength hprepare hcheckedGate
  have hlengthTail :=
    run_linkPrograms hpositive hlength hlengthRun hprepareTail
  have hrun :=
    run_linkPrograms hpositive hlength hmap hlengthTail
  simpa [balancedValidationSummaryProgram,
    balancedValidationSummaryFuel] using hrun

private theorem nonzeroAtomCount_le_length
    (values : List ℕ) :
    nonzeroAtomCount values ≤ values.length := by
  induction values with
  | nil =>
      simp [nonzeroAtomCount]
  | cons head tail inductionHypothesis =>
      by_cases hhead : head = 0
      · simp [nonzeroAtomCount, hhead]
        omega
      · simp [nonzeroAtomCount, hhead]
        omega

private theorem nonzeroAtomCount_eq_length_iff
    (values : List ℕ) :
    nonzeroAtomCount values = values.length ↔
      ∀ value, value ∈ values → value ≠ 0 := by
  induction values with
  | nil =>
      simp [nonzeroAtomCount]
  | cons head tail inductionHypothesis =>
      by_cases hhead : head = 0
      · constructor
        · intro hcount
          have hle := nonzeroAtomCount_le_length tail
          simp [nonzeroAtomCount, hhead] at hcount
          omega
        · intro hall
          exact False.elim <| hall head (by simp) hhead
      · constructor
        · intro hcount value hvalue
          rcases List.mem_cons.mp hvalue with rfl | htail
          · exact hhead
          · apply (inductionHypothesis.mp ?_) value htail
            simp [nonzeroAtomCount, hhead] at hcount
            omega
        · intro hall
          have htail :
              nonzeroAtomCount tail = tail.length := by
            apply inductionHypothesis.mpr
            intro value hvalue
            exact hall value (List.mem_cons_of_mem head hvalue)
          simp [nonzeroAtomCount, hhead, htail, Nat.add_comm]

theorem balancedValidationAllOutput_ne_zero_iff
    (inputLength raw : ℕ) (output : ℕ → ℕ) :
    balancedValidationAllOutput inputLength raw output ≠ 0 ↔
      ∃ codes,
        decodeBalancedList raw = some codes ∧
          ∀ code, code ∈ codes →
            output (nativeInputRequest inputLength code) ≠ 0 := by
  let outputs := balancedValidationMapOutputs inputLength raw output
  constructor
  · intro hnonzero
    have haccepts :
        balancedValidationAllAccepts inputLength raw output := by
      by_contra hrejected
      exact hnonzero <| by
        simp [balancedValidationAllOutput, hrejected]
    have hflag :
        balancedValidationMapFlag raw ≠ 0 := by
      exact haccepts.1
    cases hdecode : decodeBalancedList raw with
    | none =>
        exact False.elim <| hflag <|
          (balancedCanonicalityOutput_eq_zero_iff raw).2 hdecode
    | some codes =>
        have hallOutputs :
            ∀ value, value ∈ outputs → value ≠ 0 :=
          (nonzeroAtomCount_eq_length_iff outputs).1 haccepts.2
        refine ⟨codes, rfl, ?_⟩
        intro code hcode
        apply hallOutputs
        dsimp only [outputs, balancedValidationMapOutputs,
          balancedValidationMapRequests,
          balancedValidationMapCodes]
        simp only [hdecode, Option.getD_some]
        exact List.mem_map.mpr
          ⟨nativeInputRequest inputLength code,
            List.mem_map.mpr ⟨code, hcode, rfl⟩, rfl⟩
  · rintro ⟨codes, hdecode, hall⟩
    have hflag :
        balancedValidationMapFlag raw = 1 := by
      apply (balancedCanonicalityOutput_eq_one_iff raw).2
      simp [hdecode]
    have hallOutputs :
        ∀ value, value ∈ outputs → value ≠ 0 := by
      intro value hvalue
      have hmapped :
          value ∈
            codes.map fun code =>
              output (nativeInputRequest inputLength code) := by
        simpa [outputs, balancedValidationMapOutputs,
          balancedValidationMapRequests,
          balancedValidationMapCodes, hdecode] using hvalue
      rcases List.mem_map.mp hmapped with ⟨code, hcode, rfl⟩
      exact hall code hcode
    have hcount :
        nonzeroAtomCount outputs = outputs.length :=
      (nonzeroAtomCount_eq_length_iff outputs).2 hallOutputs
    have haccepts :
        balancedValidationAllAccepts inputLength raw output := by
      exact ⟨by omega, hcount⟩
    rw [show
      balancedValidationAllOutput inputLength raw output =
          Nat.pair 1 raw by
        simp [balancedValidationAllOutput, haccepts]]
    have hleft := Nat.left_le_pair 1 raw
    omega

theorem balancedValidationSummaryOutput_ne_zero_iff
    (inputLength raw : ℕ) (output : ℕ → ℕ) :
    balancedValidationSummaryOutput inputLength raw output ≠ 0 ↔
      ∃ codes,
        decodeBalancedList raw = some codes ∧
          ∀ code, code ∈ codes →
            output (nativeInputRequest inputLength code) ≠ 0 := by
  calc
    balancedValidationSummaryOutput inputLength raw output ≠ 0 ↔
        balancedValidationAllOutput inputLength raw output ≠ 0 := by
      unfold balancedValidationSummaryOutput
      by_cases hrejected :
          balancedValidationAllOutput inputLength raw output = 0
      · simp [hrejected]
      · rw [if_neg hrejected]
        constructor
        · intro _
          exact hrejected
        · intro _ hzero
          have hleft :=
            Nat.left_le_pair 1
              (balancedValidationSummaryData inputLength raw output)
          rw [hzero] at hleft
          omega
    _ ↔ _ :=
      balancedValidationAllOutput_ne_zero_iff inputLength raw output

theorem balancedValidationSummaryOutput_payload
    (inputLength raw : ℕ) (output : ℕ → ℕ)
    (hnonzero :
      balancedValidationSummaryOutput inputLength raw output ≠ 0) :
    (Nat.unpair
      (balancedValidationSummaryOutput inputLength raw output)).2 =
        balancedValidationSummaryData inputLength raw output := by
  unfold balancedValidationSummaryOutput at hnonzero ⊢
  by_cases hrejected :
      balancedValidationAllOutput inputLength raw output = 0
  · simp [hrejected] at hnonzero
  · simp [hrejected]

end NearCubicWires.CanonicalBalancedValidationMapProgram
