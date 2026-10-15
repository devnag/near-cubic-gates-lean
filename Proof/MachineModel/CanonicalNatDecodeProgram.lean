import Proof.MachineModel.BalancedClauseStreamFlattenProgram
import Proof.Circuits.CanonicalBalancedTraversal
import Proof.Foundations.VerifiedLinker

namespace NearCubicWires.CanonicalNatDecodeProgram

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

/-! ## Balanced bits to singleton tagged streams -/

def singletonTaggedBit (bit : ℕ) : ℕ :=
  encodeTaggedList [bit]

/-- The first 34 instructions are the unique shared balanced controller.
The four-instruction leaf handler wraps `r3` as one tagged cell; the final
instruction halts after the controller rebuilds the mapped balanced tree. -/
def balancedBitSingletonProgram : NPOracleProgram :=
  balancedTraversalController 34 38 ++
    [ .set 4 0 35
    , .pair 3 4 4 36
    , .set 5 1 37
    , .pair 5 4 3 balancedTraversalLeafReturnPc
    , .halt 0
    ]

@[simp] theorem balancedBitSingletonProgram_oracleFree :
    OracleFree balancedBitSingletonProgram := by
  rfl

theorem balancedBitSingletonProgram_controllerAt :
    BalancedTraversalControllerAt balancedBitSingletonProgram 34 38 := by
  intro pc instruction hlookup
  have hpc : pc < (balancedTraversalController 34 38).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [balancedBitSingletonProgram]
  rw [List.getElem?_append_left hpc]
  exact hlookup

def balancedBitSingletonFuel (bits : List ℕ) : ℕ :=
  balancedTraversalStructuralSteps (balancedTraversalTree bits) +
    4 * bits.length + 2

def balancedBitSingletonBits (bits : List ℕ) : ℕ :=
  balancedTraversalRequiredBits singletonTaggedBit
    (balancedTraversalTree bits) []

private theorem singletonTaggedBit_payload_bits
    (bit maximumBits : ℕ)
    (hbits : natBitLength (singletonTaggedBit bit) ≤ maximumBits) :
    natBitLength (Nat.pair bit 0) ≤ maximumBits := by
  apply (natBitLength_mono ?_).trans hbits
  simpa [singletonTaggedBit, encodeTaggedList] using
    (Nat.right_le_pair 1 (Nat.pair bit 0))

private theorem singletonTaggedBit_zero_bits
    (bit maximumBits : ℕ)
    (hbits : natBitLength (singletonTaggedBit bit) ≤ maximumBits) :
    natBitLength 0 ≤ maximumBits := by
  apply (natBitLength_mono ?_).trans hbits
  exact Nat.zero_le _

private theorem singletonTaggedBit_one_bits
    (bit maximumBits : ℕ)
    (hbits : natBitLength (singletonTaggedBit bit) ≤ maximumBits) :
    natBitLength 1 ≤ maximumBits := by
  apply (natBitLength_mono ?_).trans hbits
  exact Nat.left_le_pair 1 (Nat.pair bit 0)

private theorem run_balancedBitSingletonLeaf
    (bit maximumBits : ℕ) (entry : NPOracleState)
    (hpc : entry.pc = 34)
    (hcurrent : entry.registers 0 = Nat.pair 1 bit)
    (hatom : entry.registers 3 = bit)
    (hbits : natBitLength (singletonTaggedBit bit) ≤ maximumBits) :
    ∃ finish,
      RunsToIn balancedBitSingletonProgram maximumBits 4 entry finish ∧
      finish.pc = balancedTraversalLeafReturnPc ∧
      finish.registers 0 = entry.registers 0 ∧
      finish.registers 2 = entry.registers 2 ∧
      finish.registers 3 = singletonTaggedBit bit ∧
      SameTraversalContextFrom 9 entry finish := by
  let state1 := (entry.write 4 0).jump 35
  let state2 := (state1.write 4 (Nat.pair bit 0)).jump 36
  let state3 := (state2.write 5 1).jump 37
  let finish :=
    (state3.write 3 (singletonTaggedBit bit)).jump
      balancedTraversalLeafReturnPc
  have hzero := singletonTaggedBit_zero_bits bit maximumBits hbits
  have hone := singletonTaggedBit_one_bits bit maximumBits hbits
  have hpayload :=
    singletonTaggedBit_payload_bits bit maximumBits hbits
  have hruns :
      RunsToIn balancedBitSingletonProgram maximumBits 4 entry finish := by
    intro extra
    rw [show 4 + extra = (3 + extra) + 1 by omega]
    rw [run_set_instruction (fuel := 3 + extra)
      (by rfl) hpc hzero]
    change
      runNPOracleProgram balancedBitSingletonProgram maximumBits
          (3 + extra) state1 =
        runNPOracleProgram balancedBitSingletonProgram maximumBits
          extra finish
    rw [show 3 + extra = (2 + extra) + 1 by omega]
    rw [run_pair_instruction (fuel := 2 + extra)
      (value := Nat.pair bit 0) (by rfl) rfl
      (by simp [state1, hatom]) hpayload]
    change
      runNPOracleProgram balancedBitSingletonProgram maximumBits
          (2 + extra) state2 =
        runNPOracleProgram balancedBitSingletonProgram maximumBits
          extra finish
    rw [show 2 + extra = (1 + extra) + 1 by omega]
    rw [run_set_instruction (fuel := 1 + extra)
      (by rfl) rfl hone]
    change
      runNPOracleProgram balancedBitSingletonProgram maximumBits
          (1 + extra) state3 =
        runNPOracleProgram balancedBitSingletonProgram maximumBits
          extra finish
    rw [show 1 + extra = extra + 1 by omega]
    rw [run_pair_instruction (fuel := extra)
      (value := singletonTaggedBit bit) (by rfl) rfl
      (by
        simp [state3, state2, state1, singletonTaggedBit,
          encodeTaggedList])
      hbits]
  refine ⟨finish, hruns, rfl, ?_, ?_, ?_, ?_⟩
  · simp [finish, state3, state2, state1, hcurrent,
      NPOracleState.write, NPOracleState.jump]
  · simp [finish, state3, state2, state1,
      NPOracleState.write, NPOracleState.jump]
  · simp [finish]
  · refine ⟨?_, ?_⟩
    · simp [finish, state3, state2, state1,
        NPOracleState.write, NPOracleState.jump]
    · intro register hregister
      have hthree : register ≠ 3 := by omega
      have hfour : register ≠ 4 := by omega
      have hfive : register ≠ 5 := by omega
      simp [finish, state3, state2, state1,
        NPOracleState.write, NPOracleState.jump,
        hthree, hfour, hfive]

theorem run_balancedBitSingletonProgram
    (inputLength : ℕ) (bits : List ℕ) :
    runNPOracleProgram balancedBitSingletonProgram
        (balancedBitSingletonBits bits)
        (balancedBitSingletonFuel bits)
        (initialNPOracleState inputLength
          (encodeBalancedList bits)) =
      some
        (encodeBalancedList (bits.map singletonTaggedBit)) := by
  let initial :=
    initialNPOracleState inputLength (encodeBalancedList bits)
  have hfit :
      BalancedTraversalFits (balancedBitSingletonBits bits)
        singletonTaggedBit (balancedTraversalTree bits) [] :=
    (balancedTraversalRequiredBits_le_iff
      (balancedBitSingletonBits bits) singletonTaggedBit
      (balancedTraversalTree bits) []).mp (le_refl _)
  obtain ⟨finish, hruns, hpc, houtput, _hstack, _hpersistent⟩ :=
    run_balancedTraversal singletonTaggedBit (fun _ => 4) bits
      initial inputLength 9 (by omega)
      balancedBitSingletonProgram_controllerAt
      (by rfl)
      (by simp [initial, initialNPOracleState])
      (by simp [initial, initialNPOracleState])
      (by simp [initial, initialNPOracleState])
      hfit
      (by
        intro bit hbit entry hentryPc hcurrent hatom hbits
          _hentryInputLength
        exact run_balancedBitSingletonLeaf bit
          (balancedBitSingletonBits bits) entry hentryPc
          hcurrent hatom hbits)
  have houtputBits :
      natBitLength
          (encodeBalancedList (bits.map singletonTaggedBit)) ≤
        balancedBitSingletonBits bits :=
    by
      simpa [balancedTraversalTree_map_code] using hfit.output
  have hhalt :
      runNPOracleProgram balancedBitSingletonProgram
          (balancedBitSingletonBits bits) 1 finish =
        some (encodeBalancedList (bits.map singletonTaggedBit)) := by
    exact run_halt_instruction (fuel := 0) (by rfl) hpc houtput houtputBits
  rw [show balancedBitSingletonFuel bits =
      (balancedTraversalStructuralSteps (balancedTraversalTree bits) +
        (bits.map fun _ => 4).sum + 1) + 1 by
    simp [balancedBitSingletonFuel]
    omega]
  rw [hruns]
  exact hhalt

/-! The raw canonicality path reasons first about a structural tree and only
later checks midpoint rebalancing.  This corollary exposes the same controller
and leaf handler at that intermediate boundary. -/

def balancedBitSingletonTreeFuel
    (tree : BalancedTraversalTree) : ℕ :=
  balancedTraversalStructuralSteps tree + 4 * tree.atoms.length + 2

def balancedBitSingletonTreeBits
    (tree : BalancedTraversalTree) : ℕ :=
  balancedTraversalRequiredBits singletonTaggedBit tree []

theorem run_balancedBitSingletonTreeProgram
    (inputLength : ℕ) (tree : BalancedTraversalTree) :
    runNPOracleProgram balancedBitSingletonProgram
        (balancedBitSingletonTreeBits tree)
        (balancedBitSingletonTreeFuel tree)
        (initialNPOracleState inputLength tree.code) =
      some ((tree.map singletonTaggedBit).code) := by
  let initial := initialNPOracleState inputLength tree.code
  have hfit :
      BalancedTraversalFits (balancedBitSingletonTreeBits tree)
        singletonTaggedBit tree [] :=
    (balancedTraversalRequiredBits_le_iff
      (balancedBitSingletonTreeBits tree) singletonTaggedBit tree []).mp
      (le_refl _)
  have hhandler :
      ∀ bit, bit ∈ tree.atoms →
        ∀ entry : NPOracleState,
          entry.pc = 34 →
          entry.registers 0 = Nat.pair 1 bit →
          entry.registers 3 = bit →
          natBitLength (singletonTaggedBit bit) ≤
            balancedBitSingletonTreeBits tree →
          entry.registers 1 = inputLength →
          ∃ finish,
            RunsToIn balancedBitSingletonProgram
              (balancedBitSingletonTreeBits tree) 4 entry finish ∧
            finish.pc = balancedTraversalLeafReturnPc ∧
            finish.registers 0 = entry.registers 0 ∧
            finish.registers 2 = entry.registers 2 ∧
            finish.registers 3 = singletonTaggedBit bit ∧
            SameTraversalContextFrom 9 entry finish := by
    intro bit _hbit entry hentryPc hcurrent hatom hbits
      _hentryInputLength
    exact run_balancedBitSingletonLeaf bit
      (balancedBitSingletonTreeBits tree) entry hentryPc
      hcurrent hatom hbits
  rcases run_balancedTraversal_subtree singletonTaggedBit (fun _ => 4)
      tree [] initial inputLength 9 (by omega)
      balancedBitSingletonProgram_controllerAt
      (by rfl)
      (by simp [initial, initialNPOracleState])
      (by simp [initial, initialNPOracleState,
        encodeBalancedTraversalStack, encodeTaggedList])
      (by simp [initial, initialNPOracleState])
      hfit hhandler with
    ⟨atResume, htreeRuns, hatResumePc, hatResumeCurrent,
      hatResumeStack, _htreePersistent⟩
  have hfinish :
      runNPOracleProgram balancedBitSingletonProgram
          (balancedBitSingletonTreeBits tree) 2 atResume =
        some ((tree.map singletonTaggedBit).code) := by
    rw [show (2 : ℕ) = 1 + 1 by omega]
    rw [run_branchZero_instruction
      (program := balancedBitSingletonProgram)
      (maximumBits := balancedBitSingletonTreeBits tree)
      (fuel := 1) (pc := 15) (register := 2)
      (zeroTarget := 38) (nonzeroTarget := 16)
      (by rfl) hatResumePc]
    rw [show atResume.registers 2 = 0 by
      simpa [encodeBalancedTraversalStack, encodeTaggedList] using
        hatResumeStack]
    rw [if_pos rfl]
    exact run_halt_instruction
      (program := balancedBitSingletonProgram)
      (maximumBits := balancedBitSingletonTreeBits tree)
      (fuel := 0) (pc := 38) (outputRegister := 0)
      (value := (tree.map singletonTaggedBit).code)
      (by rfl) (by rfl)
      (by simpa [NPOracleState.jump] using hatResumeCurrent)
      hfit.output
  have hsteps :=
    balancedTraversalSteps_eq_structural tree (fun _ => 4)
  have htreeFuel :
      balancedTraversalSteps (fun _ => 4) tree + 2 =
        balancedBitSingletonTreeFuel tree := by
    rw [hsteps]
    simp [balancedBitSingletonTreeFuel]
    omega
  rw [← htreeFuel]
  rw [htreeRuns 2]
  exact hfinish

/-! ## Reuse the proven balanced stream flattener -/

def balancedBitsToTaggedProgram : NPOracleProgram :=
  linkPrograms balancedBitSingletonProgram
    balancedClauseStreamFlattenProgram

def balancedBitsToTaggedFuel (bits : List ℕ) : ℕ :=
  linkFuel balancedClauseStreamFlattenProgram
    (balancedBitSingletonFuel bits)
    (balancedClauseStreamFlattenFuel (bits.map fun bit => [bit]))

def balancedBitsToTaggedBits
    (inputLength : ℕ) (bits : List ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (balancedBitSingletonBits bits)
      (balancedClauseStreamFlattenMaximumBits
        (bits.map fun bit => [bit]))

@[simp] theorem balancedBitsToTaggedProgram_oracleFree :
    OracleFree balancedBitsToTaggedProgram := by
  exact oracleFree_linkPrograms
    balancedBitSingletonProgram_oracleFree
    balancedClauseStreamFlattenProgram_oracleFree

private theorem singletonStreams_flatten (bits : List ℕ) :
    (bits.map fun bit => [bit]).flatten = bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [ih]

theorem run_balancedBitsToTaggedProgram
    (inputLength : ℕ) (bits : List ℕ) :
    runNPOracleProgram balancedBitsToTaggedProgram
        (balancedBitsToTaggedBits inputLength bits)
        (balancedBitsToTaggedFuel bits)
        (initialNPOracleState inputLength
          (encodeBalancedList bits)) =
      some (encodeTaggedList bits) := by
  let maximumBits := balancedBitsToTaggedBits inputLength bits
  have hinputBits : natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hsingletonBits :
      balancedBitSingletonBits bits ≤ maximumBits := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hflattenBits :
      balancedClauseStreamFlattenMaximumBits
          (bits.map fun bit => [bit]) ≤ maximumBits := by
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hpositive : 1 ≤ maximumBits := by
    exact (by
      unfold natBitLength
      omega : 1 ≤ natBitLength inputLength).trans hinputBits
  apply run_linkPrograms hpositive hinputBits
  · exact run_bits_mono
      (run_balancedBitSingletonProgram inputLength bits)
      hsingletonBits
  · have hrun :=
      run_bits_mono
        (run_balancedClauseStreamFlattenProgram
          (bits.map fun bit => [bit]) inputLength)
        hflattenBits
    have hstreams :
        (bits.map fun bit => [bit]).map encodeTaggedList =
          bits.map singletonTaggedBit := by
      rw [List.map_map]
      rfl
    rw [hstreams, singletonStreams_flatten] at hrun
    exact hrun

/-! ## Tagged little-endian bit arithmetic fold -/

def taggedBitFoldProgram : NPOracleProgram :=
  [ .set 2 0 1
  , .set 3 1 2
  , .branchZero 0 15 3
  , .unpairRight 0 5 4
  , .unpairLeft 5 4 5
  , .unpairRight 5 0 6
  , .branchZero 4 8 7
  , .add 2 3 2 8
  , .shiftLeft 3 1 3 2
  , .halt 0
  , .halt 0
  , .halt 0
  , .halt 0
  , .halt 0
  , .halt 0
  , .copy 2 0 16
  , .halt 0
  ]

@[simp] theorem taggedBitFoldProgram_oracleFree :
    OracleFree taggedBitFoldProgram := by
  rfl

def taggedBitFoldValue : List ℕ → ℕ → ℕ → ℕ
  | [], accumulator, _place => accumulator
  | bit :: bits, accumulator, place =>
      taggedBitFoldValue bits
        (if bit = 0 then accumulator else accumulator + place)
        (place + place)

private theorem shiftLeft_one_add (value : ℕ) :
    Nat.shiftLeft value 1 = value + value := by
  have hdouble : Nat.shiftLeft value 1 = 2 * value := by
    simp [Nat.shiftLeft_eq, Nat.mul_comm]
  omega

/-- One decoded bit costs six fixed instructions, plus one more when the bit
is set and the accumulator has to absorb the current place. -/
def taggedBitFoldFuelFrom : List ℕ → ℕ → ℕ
  | [], _place => 3
  | bit :: bits, place =>
      6 + (if bit = 0 then 0 else 1) +
        taggedBitFoldFuelFrom bits (place + place)

def taggedBitFoldFuel (bits : List ℕ) : ℕ :=
  2 + taggedBitFoldFuelFrom bits 1

/-- **The fold is charged by the number of decoded bits.**  Every term is
linear in the code's bit count; none grows with the decoded magnitude. -/
theorem taggedBitFoldFuelFrom_le (bits : List ℕ) (place : ℕ) :
    taggedBitFoldFuelFrom bits place ≤ 7 * bits.length + 3 := by
  induction bits generalizing place with
  | nil => simp [taggedBitFoldFuelFrom]
  | cons bit bits inductionHypothesis =>
      have htail := inductionHypothesis (place + place)
      have hstep : (if bit = 0 then 0 else 1) ≤ 1 := by
        split <;> omega
      simp only [taggedBitFoldFuelFrom, List.length_cons]
      omega

theorem taggedBitFoldFuel_le (bits : List ℕ) :
    taggedBitFoldFuel bits ≤ 7 * bits.length + 5 := by
  have hfold := taggedBitFoldFuelFrom_le bits 1
  unfold taggedBitFoldFuel
  omega

private def taggedBitFoldWorkingValues :
    List ℕ → ℕ → ℕ → List ℕ
  | [], accumulator, place =>
      [0, 1, accumulator, place]
  | bit :: bits, accumulator, place =>
      let restCode := encodeTaggedList bits
      let payload := Nat.pair bit restCode
      let nextAccumulator :=
        if bit = 0 then accumulator else accumulator + place
      let nextPlace := place + place
      [ encodeTaggedList (bit :: bits), payload, bit, restCode,
        0, 1, accumulator, place, nextAccumulator, nextPlace ] ++
        taggedBitFoldWorkingValues bits nextAccumulator nextPlace

private def taggedBitFoldWorkBound
    (bits : List ℕ) : ℕ :=
  (taggedBitFoldWorkingValues bits 0 1).foldr max 0

def taggedBitFoldBits (bits : List ℕ) : ℕ :=
  natBitLength (taggedBitFoldWorkBound bits)

private theorem le_foldr_max_of_mem
    {value : ℕ} {values : List ℕ} (hmem : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact (ih hmem).trans (Nat.le_max_right _ _)

private theorem taggedBitFoldWorkingValue_bits
    (bits : List ℕ) {value : ℕ}
    (hmem : value ∈ taggedBitFoldWorkingValues bits 0 1) :
    natBitLength value ≤ taggedBitFoldBits bits := by
  unfold taggedBitFoldBits taggedBitFoldWorkBound
  exact natBitLength_mono (le_foldr_max_of_mem hmem)

private theorem taggedBitFoldValue_append
    (left right : List ℕ) (accumulator place : ℕ) :
    taggedBitFoldValue (left ++ right) accumulator place =
      taggedBitFoldValue right
        (taggedBitFoldValue left accumulator place)
        (place * 2 ^ left.length) := by
  induction left generalizing accumulator place with
  | nil => simp [taggedBitFoldValue]
  | cons bit bits ih =>
      simp only [List.cons_append, taggedBitFoldValue, List.length_cons]
      rw [ih]
      rw [show (place + place) * 2 ^ bits.length =
          place * 2 ^ (bits.length + 1) by
        rw [pow_succ]
        ring]

private theorem taggedBitFoldValue_bool
    (bits : List Bool) (accumulator place : ℕ) :
    taggedBitFoldValue (bits.map Bool.toNat) accumulator place =
      accumulator + place * bitsValue bits := by
  induction bits generalizing accumulator place with
  | nil => simp [taggedBitFoldValue, bitsValue]
  | cons bit bits ih =>
      cases bit
      · simp [taggedBitFoldValue, bitsValue, ih]
        ring
      · simp [taggedBitFoldValue, bitsValue, ih]
        ring

theorem taggedBitFoldValue_boolBits
    (bits : List Bool) :
    taggedBitFoldValue (bits.map Bool.toNat) 0 1 =
      bitsValue bits := by
  simpa using taggedBitFoldValue_bool bits 0 1

private theorem run_taggedBitFoldFrom
    (bits : List ℕ) (accumulator place maximumBits : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 2)
    (hcursor : state.registers 0 = encodeTaggedList bits)
    (haccumulator : state.registers 2 = accumulator)
    (hplace : state.registers 3 = place)
    (hfit : ∀ value,
      value ∈ taggedBitFoldWorkingValues bits accumulator place →
        natBitLength value ≤ maximumBits) :
    runNPOracleProgram taggedBitFoldProgram maximumBits
        (taggedBitFoldFuelFrom bits place) state =
      some (taggedBitFoldValue bits accumulator place) := by
  induction bits generalizing accumulator place state with
  | nil =>
      have haccumulatorBits :
          natBitLength accumulator ≤ maximumBits :=
        hfit accumulator (by simp [taggedBitFoldWorkingValues])
      let state1 := state.jump 15
      let state2 := (state1.write 0 accumulator).jump 16
      rw [show taggedBitFoldFuelFrom [] place = 2 + 1 by
        rfl]
      rw [run_branchZero_instruction (fuel := 2)
        (by rfl) hpc]
      rw [hcursor]
      simp only [encodeTaggedList, if_pos]
      change
        runNPOracleProgram taggedBitFoldProgram maximumBits 2 state1 =
          some accumulator
      rw [show 2 = 1 + 1 by omega]
      rw [run_copy_instruction (fuel := 1)
        (value := accumulator) (by rfl) rfl
        (by simp [state1, haccumulator])
        haccumulatorBits]
      change
        runNPOracleProgram taggedBitFoldProgram maximumBits 1 state2 =
          some accumulator
      exact run_halt_instruction (fuel := 0) (by rfl) rfl
        (by simp [state2]) haccumulatorBits
  | cons bit bits ih =>
      let restCode := encodeTaggedList bits
      let payload := Nat.pair bit restCode
      let nextAccumulator :=
        if bit = 0 then accumulator else accumulator + place
      let nextPlace := place + place
      have hcursorNonzero :
          encodeTaggedList (bit :: bits) ≠ 0 := by
        have hpositive :
            0 < Nat.pair 1 payload :=
          lt_of_lt_of_le (by omega) (Nat.left_le_pair 1 payload)
        simpa [encodeTaggedList, payload] using hpositive.ne'
      have hpayloadBits :
          natBitLength payload ≤ maximumBits :=
        hfit payload (by
          simp [taggedBitFoldWorkingValues, payload, restCode])
      have hbitBits :
          natBitLength bit ≤ maximumBits :=
        hfit bit (by
          simp [taggedBitFoldWorkingValues])
      have hrestBits :
          natBitLength restCode ≤ maximumBits :=
        hfit restCode (by
          simp [taggedBitFoldWorkingValues, restCode])
      have hnextAccumulatorBits :
          natBitLength nextAccumulator ≤ maximumBits :=
        hfit nextAccumulator (by
          simp [taggedBitFoldWorkingValues, nextAccumulator])
      have hnextPlaceBits :
          natBitLength nextPlace ≤ maximumBits :=
        hfit nextPlace (by
          simp [taggedBitFoldWorkingValues, nextPlace])
      have hfitRest :
          ∀ value,
            value ∈
                taggedBitFoldWorkingValues bits
                  nextAccumulator nextPlace →
              natBitLength value ≤ maximumBits := by
        intro value hvalue
        apply hfit value
        simp [taggedBitFoldWorkingValues, nextAccumulator,
          nextPlace, hvalue]
      let state1 := state.jump 3
      let state2 := (state1.write 5 payload).jump 4
      let state3 := (state2.write 4 bit).jump 5
      let state4 := (state3.write 0 restCode).jump 6
      let state5 :=
        state4.jump (if bit = 0 then 8 else 7)
      have hplaceState : state4.registers 3 = place := by
        simp [state4, state3, state2, state1, NPOracleState.write,
          NPOracleState.jump, hplace]
      have haccumulatorState : state4.registers 2 = accumulator := by
        simp [state4, state3, state2, state1, NPOracleState.write,
          NPOracleState.jump, haccumulator]
      rw [show taggedBitFoldFuelFrom (bit :: bits) place =
          (5 + (if bit = 0 then 0 else 1) +
            taggedBitFoldFuelFrom bits nextPlace) + 1 by
        simp [taggedBitFoldFuelFrom, nextPlace]
        omega]
      rw [run_branchZero_instruction
        (fuel :=
          5 + (if bit = 0 then 0 else 1) +
            taggedBitFoldFuelFrom bits nextPlace)
        (by rfl) hpc]
      rw [hcursor, if_neg hcursorNonzero]
      change
        runNPOracleProgram taggedBitFoldProgram maximumBits
            (5 + (if bit = 0 then 0 else 1) +
              taggedBitFoldFuelFrom bits nextPlace) state1 =
          some
            (taggedBitFoldValue (bit :: bits) accumulator place)
      rw [show
          5 + (if bit = 0 then 0 else 1) +
              taggedBitFoldFuelFrom bits nextPlace =
            (4 + (if bit = 0 then 0 else 1) +
              taggedBitFoldFuelFrom bits nextPlace) + 1 by
        omega]
      rw [run_unpairRight_instruction
        (value := payload)
        (fuel :=
          4 + (if bit = 0 then 0 else 1) +
            taggedBitFoldFuelFrom bits nextPlace)
        (by rfl) rfl
        (by
          simp [state1, hcursor, encodeTaggedList, payload,
            restCode])
        hpayloadBits]
      change
        runNPOracleProgram taggedBitFoldProgram maximumBits
            (4 + (if bit = 0 then 0 else 1) +
              taggedBitFoldFuelFrom bits nextPlace) state2 =
          some
            (taggedBitFoldValue (bit :: bits) accumulator place)
      rw [show
          4 + (if bit = 0 then 0 else 1) +
              taggedBitFoldFuelFrom bits nextPlace =
            (3 + (if bit = 0 then 0 else 1) +
              taggedBitFoldFuelFrom bits nextPlace) + 1 by
        omega]
      rw [run_unpairLeft_instruction
        (value := bit)
        (fuel :=
          3 + (if bit = 0 then 0 else 1) +
            taggedBitFoldFuelFrom bits nextPlace)
        (by rfl) rfl
        (by simp [state2, state1, payload])
        hbitBits]
      change
        runNPOracleProgram taggedBitFoldProgram maximumBits
            (3 + (if bit = 0 then 0 else 1) +
              taggedBitFoldFuelFrom bits nextPlace) state3 =
          some
            (taggedBitFoldValue (bit :: bits) accumulator place)
      rw [show
          3 + (if bit = 0 then 0 else 1) +
              taggedBitFoldFuelFrom bits nextPlace =
            (2 + (if bit = 0 then 0 else 1) +
              taggedBitFoldFuelFrom bits nextPlace) + 1 by
        omega]
      rw [run_unpairRight_instruction
        (value := restCode)
        (fuel :=
          2 + (if bit = 0 then 0 else 1) +
            taggedBitFoldFuelFrom bits nextPlace)
        (by rfl) rfl
        (by simp [state3, state2, state1, payload, restCode])
        hrestBits]
      change
        runNPOracleProgram taggedBitFoldProgram maximumBits
            (2 + (if bit = 0 then 0 else 1) +
              taggedBitFoldFuelFrom bits nextPlace) state4 =
          some
            (taggedBitFoldValue (bit :: bits) accumulator place)
      rw [show
          2 + (if bit = 0 then 0 else 1) +
              taggedBitFoldFuelFrom bits nextPlace =
            (1 + (if bit = 0 then 0 else 1) +
              taggedBitFoldFuelFrom bits nextPlace) + 1 by
        omega]
      rw [run_branchZero_instruction
        (fuel :=
          1 + (if bit = 0 then 0 else 1) +
            taggedBitFoldFuelFrom bits nextPlace)
        (by rfl) rfl]
      change
        runNPOracleProgram taggedBitFoldProgram maximumBits
            (1 + (if bit = 0 then 0 else 1) +
              taggedBitFoldFuelFrom bits nextPlace) state5 =
          some
            (taggedBitFoldValue (bit :: bits) accumulator place)
      by_cases hbit : bit = 0
      · simp only [state5, taggedBitFoldValue]
        simp only [if_pos hbit]
        let state6 :=
          ((state4.jump 8).write 3 nextPlace).jump 2
        rw [show
            1 + 0 + taggedBitFoldFuelFrom bits nextPlace =
              taggedBitFoldFuelFrom bits nextPlace + 1 by
          omega]
        rw [run_shiftLeft_instruction
          (fuel := taggedBitFoldFuelFrom bits nextPlace)
          (value := nextPlace) (by rfl) rfl
          (by
            simp only [NPOracleState.jump]
            rw [hplaceState]
            exact shiftLeft_one_add place)
          hnextPlaceBits]
        change
          runNPOracleProgram taggedBitFoldProgram maximumBits
              (taggedBitFoldFuelFrom bits nextPlace) state6 =
            some
              (taggedBitFoldValue bits accumulator nextPlace)
        apply ih accumulator nextPlace state6
        · rfl
        · simp [state6, state4, restCode, NPOracleState.write,
            NPOracleState.jump]
        · simp [state6, NPOracleState.write, NPOracleState.jump,
            haccumulatorState]
        · simp [state6, NPOracleState.write, NPOracleState.jump]
        · simpa [nextAccumulator, hbit] using hfitRest
      · simp only [state5, taggedBitFoldValue]
        simp only [if_neg hbit]
        let state6 :=
          ((state4.jump 7).write 2 (accumulator + place)).jump 8
        let state7 := (state6.write 3 nextPlace).jump 2
        rw [show
            1 + 1 + taggedBitFoldFuelFrom bits nextPlace =
              (taggedBitFoldFuelFrom bits nextPlace + 1) + 1 by
          omega]
        rw [run_add_instruction
          (fuel := taggedBitFoldFuelFrom bits nextPlace + 1)
          (value := accumulator + place) (by rfl) rfl
          (by
            simp only [NPOracleState.jump]
            rw [haccumulatorState, hplaceState])
          (by simpa [nextAccumulator, hbit] using
            hnextAccumulatorBits)]
        change
          runNPOracleProgram taggedBitFoldProgram maximumBits
              (taggedBitFoldFuelFrom bits nextPlace + 1) state6 =
            some
              (taggedBitFoldValue bits (accumulator + place) nextPlace)
        rw [run_shiftLeft_instruction
          (fuel := taggedBitFoldFuelFrom bits nextPlace)
          (value := nextPlace) (by rfl) rfl
          (by
            simp only [state6, NPOracleState.write, NPOracleState.jump]
            rw [show
                (if (3 : ℕ) = 2 then accumulator + place
                  else state4.registers 3) = place by
              simp [hplaceState]]
            exact shiftLeft_one_add place)
          hnextPlaceBits]
        change
          runNPOracleProgram taggedBitFoldProgram maximumBits
              (taggedBitFoldFuelFrom bits nextPlace) state7 =
            some
              (taggedBitFoldValue bits (accumulator + place) nextPlace)
        apply ih (accumulator + place) nextPlace state7
        · rfl
        · simp [state7, state6, state4, restCode,
            NPOracleState.write, NPOracleState.jump]
        · simp [state7, state6, NPOracleState.write,
            NPOracleState.jump]
        · simp [state7, NPOracleState.write, NPOracleState.jump]
        · simpa [nextAccumulator, hbit] using hfitRest

def taggedBitFoldMaximumBits
    (inputLength : ℕ) (bits : List ℕ) : ℕ :=
  max (natBitLength inputLength) (taggedBitFoldBits bits)

theorem run_taggedBitFoldProgram
    (inputLength : ℕ) (bits : List ℕ) :
    runNPOracleProgram taggedBitFoldProgram
        (taggedBitFoldMaximumBits inputLength bits)
        (taggedBitFoldFuel bits)
        (initialNPOracleState inputLength
          (encodeTaggedList bits)) =
      some (taggedBitFoldValue bits 0 1) := by
  let maximumBits := taggedBitFoldMaximumBits inputLength bits
  let initial :=
    initialNPOracleState inputLength (encodeTaggedList bits)
  let state1 := (initial.write 2 0).jump 1
  let state2 := (state1.write 3 1).jump 2
  have hzeroBits : natBitLength 0 ≤ maximumBits := by
    apply (taggedBitFoldWorkingValue_bits bits ?_).trans
      (Nat.le_max_right _ _)
    cases bits <;> simp [taggedBitFoldWorkingValues]
  have honeBits : natBitLength 1 ≤ maximumBits := by
    apply (taggedBitFoldWorkingValue_bits bits ?_).trans
      (Nat.le_max_right _ _)
    cases bits <;> simp [taggedBitFoldWorkingValues]
  rw [show taggedBitFoldFuel bits =
      (1 + taggedBitFoldFuelFrom bits 1) + 1 by
    simp [taggedBitFoldFuel]
    omega]
  change
    runNPOracleProgram taggedBitFoldProgram maximumBits
        ((1 + taggedBitFoldFuelFrom bits 1) + 1) initial =
      some (taggedBitFoldValue bits 0 1)
  rw [run_set_instruction
    (fuel := 1 + taggedBitFoldFuelFrom bits 1)
    (pc := 0) (register := 2) (value := 0) (next := 1)
    (by rfl) (by rfl) hzeroBits]
  change
    runNPOracleProgram taggedBitFoldProgram maximumBits
        (1 + taggedBitFoldFuelFrom bits 1) state1 =
      some (taggedBitFoldValue bits 0 1)
  rw [show 1 + taggedBitFoldFuelFrom bits 1 =
      taggedBitFoldFuelFrom bits 1 + 1 by omega]
  rw [run_set_instruction
    (fuel := taggedBitFoldFuelFrom bits 1)
    (pc := 1) (register := 3) (value := 1) (next := 2)
    (by rfl) rfl honeBits]
  apply run_taggedBitFoldFrom bits 0 1 maximumBits state2
  · rfl
  · simp [state2, state1, initial, initialNPOracleState,
      NPOracleState.write]
  · simp [state2, state1, initial, NPOracleState.write]
  · simp [state2]
  · intro value hvalue
    exact (taggedBitFoldWorkingValue_bits bits hvalue).trans
      (Nat.le_max_right _ _)

/-! ## One public decoder for `encodeNat` -/

def canonicalNatDecodeRawBits (value : ℕ) : List ℕ :=
  value.bits.map boolCode

def canonicalNatDecodeProgram : NPOracleProgram :=
  linkPrograms balancedBitsToTaggedProgram taggedBitFoldProgram

def canonicalNatDecodeListFuel (bits : List ℕ) : ℕ :=
  linkFuel taggedBitFoldProgram
    (balancedBitsToTaggedFuel bits)
    (taggedBitFoldFuel bits)

def canonicalNatDecodeListBits
    (inputLength : ℕ) (bits : List ℕ) : ℕ :=
  max
    (balancedBitsToTaggedBits inputLength bits)
    (taggedBitFoldMaximumBits inputLength bits)

def canonicalNatDecodeFuel (value : ℕ) : ℕ :=
  canonicalNatDecodeListFuel (canonicalNatDecodeRawBits value)

def canonicalNatDecodeBits
    (inputLength value : ℕ) : ℕ :=
  canonicalNatDecodeListBits inputLength
    (canonicalNatDecodeRawBits value)

@[simp] theorem canonicalNatDecodeProgram_oracleFree :
    OracleFree canonicalNatDecodeProgram := by
  exact oracleFree_linkPrograms
    balancedBitsToTaggedProgram_oracleFree
    taggedBitFoldProgram_oracleFree

theorem canonicalNatDecodeFuel_positive (value : ℕ) :
    0 < canonicalNatDecodeFuel value := by
  unfold canonicalNatDecodeFuel canonicalNatDecodeListFuel linkFuel
  omega

theorem canonicalNatDecode_inputLength_bits
    (inputLength value : ℕ) :
    natBitLength inputLength ≤
      canonicalNatDecodeBits inputLength value := by
  unfold canonicalNatDecodeBits canonicalNatDecodeListBits
  apply (Nat.le_max_left _ _).trans
  exact Nat.le_max_left _ _

/-- The same fixed decoder has a total semantic description on every
canonical balanced list of naturals.  Nonzero atoms are interpreted as set
bits; the later encode-and-compare guard is what rejects atoms other than
`0` and `1` and noncanonical high zeroes. -/
theorem run_canonicalNatDecodeProgram_fromList
    (inputLength : ℕ) (bits : List ℕ) :
    runNPOracleProgram canonicalNatDecodeProgram
        (canonicalNatDecodeListBits inputLength bits)
        (canonicalNatDecodeListFuel bits)
        (initialNPOracleState inputLength (encodeBalancedList bits)) =
      some (taggedBitFoldValue bits 0 1) := by
  let maximumBits := canonicalNatDecodeListBits inputLength bits
  have hfirstBits :
      balancedBitsToTaggedBits inputLength bits ≤ maximumBits :=
    Nat.le_max_left _ _
  have hsecondBits :
      taggedBitFoldMaximumBits inputLength bits ≤ maximumBits :=
    Nat.le_max_right _ _
  have hinputBits : natBitLength inputLength ≤ maximumBits := by
    exact (Nat.le_max_left _ _).trans hfirstBits
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hinputBits
  apply run_linkPrograms hpositive hinputBits
  · exact run_bits_mono
      (run_balancedBitsToTaggedProgram inputLength bits) hfirstBits
  · exact run_bits_mono
      (run_taggedBitFoldProgram inputLength bits) hsecondBits

/-- Exact execution of the sole public `encodeNat` inverse.  The theorem
crosses both verified linker handoffs and ends in a native register value;
there is no host-side decoder or alternate integer representation. -/
theorem run_canonicalNatDecodeProgram
    (inputLength value : ℕ) :
    runNPOracleProgram canonicalNatDecodeProgram
        (canonicalNatDecodeBits inputLength value)
        (canonicalNatDecodeFuel value)
        (initialNPOracleState inputLength (encodeNat value)) =
      some value := by
  let rawBits := canonicalNatDecodeRawBits value
  have hrun :=
    run_canonicalNatDecodeProgram_fromList inputLength rawBits
  have hvalue :
      taggedBitFoldValue rawBits 0 1 = value := by
    change taggedBitFoldValue (value.bits.map Bool.toNat) 0 1 = value
    exact (taggedBitFoldValue_boolBits value.bits).trans
      (bitsValue_natBits value)
  rw [hvalue] at hrun
  simpa [rawBits, canonicalNatDecodeRawBits, canonicalNatDecodeBits,
    canonicalNatDecodeFuel, encodeNat, encodeBits, encodeBoolList, boolCode,
    canonicalNatDecodeListBits, canonicalNatDecodeListFuel] using hrun

end NearCubicWires.CanonicalNatDecodeProgram
