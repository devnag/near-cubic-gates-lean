import Proof.Circuits.CanonicalBalancedTraversal
import Proof.MachineModel.CanonicalSupplierSupportCompressionProgram
import Proof.Foundations.VerifiedLinker

namespace NearCubicWires.CanonicalBalancedLengthProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

def balancedTrueValues (values : List ℕ) : List Bool :=
  values.map fun _ => true

def balancedTrueTreeProgram : NPOracleProgram :=
  balancedTraversalController 34 35 ++
    [ .set 3 1 balancedTraversalLeafReturnPc
    , .halt 0
    ]

@[simp] theorem balancedTrueTreeProgram_oracleFree :
    OracleFree balancedTrueTreeProgram := by
  rfl

theorem balancedTrueTreeProgram_controllerAt :
    BalancedTraversalControllerAt balancedTrueTreeProgram 34 35 := by
  intro pc instruction hlookup
  have hpc : pc < (balancedTraversalController 34 35).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [balancedTrueTreeProgram]
  rw [List.getElem?_append_left hpc]
  exact hlookup

def balancedTrueTreeFuel (values : List ℕ) : ℕ :=
  balancedTraversalStructuralSteps (balancedTraversalTree values) +
    values.length + 2

def balancedTrueTreeBits (inputLength : ℕ) (values : List ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    balancedTraversalRequiredBits (fun _ => 1)
      (balancedTraversalTree values) []

private theorem run_balancedTrueTreeLeaf
    (atom maximumBits : ℕ) (entry : NPOracleState)
    (hpc : entry.pc = 34)
    (hcurrent : entry.registers 0 = Nat.pair 1 atom)
    (_hatom : entry.registers 3 = atom)
    (hbits : natBitLength 1 ≤ maximumBits) :
    ∃ finish,
      RunsToIn balancedTrueTreeProgram maximumBits 1 entry finish ∧
      finish.pc = balancedTraversalLeafReturnPc ∧
      finish.registers 0 = entry.registers 0 ∧
      finish.registers 2 = entry.registers 2 ∧
      finish.registers 3 = 1 ∧
      SameTraversalContextFrom 9 entry finish := by
  let finish := (entry.write 3 1).jump balancedTraversalLeafReturnPc
  have hruns :
      RunsToIn balancedTrueTreeProgram maximumBits 1 entry finish := by
    intro extra
    rw [show 1 + extra = extra + 1 by omega]
    rw [run_set_instruction (fuel := extra) (value := 1)
      (by rfl) hpc hbits]
  refine ⟨finish, hruns, rfl, ?_, ?_, ?_, ?_⟩
  · simp [finish, hcurrent, NPOracleState.write, NPOracleState.jump]
  · simp [finish, NPOracleState.write, NPOracleState.jump]
  · simp [finish]
  · refine ⟨?_, ?_⟩
    · simp [finish, NPOracleState.write, NPOracleState.jump]
    · intro register hregister
      have hthree : register ≠ 3 := by omega
      simp [finish, NPOracleState.write, NPOracleState.jump, hthree]

theorem run_balancedTrueTreeProgram
    (inputLength : ℕ) (values : List ℕ) :
    runNPOracleProgram balancedTrueTreeProgram
        (balancedTrueTreeBits inputLength values)
        (balancedTrueTreeFuel values)
        (initialNPOracleState inputLength (encodeBalancedList values)) =
      some (encodeBoolList (balancedTrueValues values)) := by
  let initial :=
    initialNPOracleState inputLength (encodeBalancedList values)
  have hfit :
      BalancedTraversalFits
        (balancedTrueTreeBits inputLength values)
        (fun _ => 1) (balancedTraversalTree values) [] :=
    (balancedTraversalRequiredBits_le_iff
      (balancedTrueTreeBits inputLength values)
      (fun _ => 1) (balancedTraversalTree values) []).mp
        (Nat.le_max_right _ _)
  obtain ⟨finish, hruns, hpc, houtput, _hstack, _hpersistent⟩ :=
    run_balancedTraversal
      (fun _ => 1) (fun _ => 1)
      values initial inputLength 9 (by omega)
      balancedTrueTreeProgram_controllerAt
      (by rfl)
      (by simp [initial, initialNPOracleState])
      (by simp [initial, initialNPOracleState])
      (by simp [initial, initialNPOracleState])
      hfit
      (by
        intro atom _hatom entry hentryPc hcurrent hatom hbits
          _hentryLength
        exact run_balancedTrueTreeLeaf atom
          (balancedTrueTreeBits inputLength values) entry
          hentryPc hcurrent hatom hbits)
  have houtputBits :
      natBitLength
          (encodeBoolList (balancedTrueValues values)) ≤
        balancedTrueTreeBits inputLength values := by
    simpa [balancedTraversalTree_map_code, balancedTrueValues,
      encodeBoolList, boolCode] using hfit.output
  have hhalt :
      runNPOracleProgram balancedTrueTreeProgram
          (balancedTrueTreeBits inputLength values) 1 finish =
        some (encodeBoolList (balancedTrueValues values)) :=
    run_halt_instruction (fuel := 0) (by rfl) hpc
      (by
        simpa [balancedTraversalTree_map_code, balancedTrueValues,
          encodeBoolList, boolCode] using houtput)
      houtputBits
  rw [show balancedTrueTreeFuel values =
      (balancedTraversalStructuralSteps (balancedTraversalTree values) +
        (values.map fun _ => 1).sum + 1) + 1 by
    simp [balancedTrueTreeFuel]]
  rw [hruns]
  exact hhalt

/-! ## Fixed count framing and projection -/

def balancedLengthCountInputProgram : NPOracleProgram :=
  [ .set 2 0 1
  , .pair 2 0 0 2
  , .halt 0
  ]

private def balancedLengthCountInputBits (treeCode : ℕ) : ℕ :=
  max (natBitLength treeCode) (natBitLength (Nat.pair 0 treeCode))

private theorem balancedLengthCountInputProgram_oracleFree :
    OracleFree balancedLengthCountInputProgram := by
  rfl

private theorem run_balancedLengthCountInputProgram
    (inputLength treeCode : ℕ) :
    runNPOracleProgram balancedLengthCountInputProgram
        (balancedLengthCountInputBits treeCode) 3
        (initialNPOracleState inputLength treeCode) =
      some (Nat.pair 0 treeCode) := by
  have hinput :
      natBitLength treeCode ≤ balancedLengthCountInputBits treeCode :=
    Nat.le_max_left _ _
  have hzero :
      natBitLength 0 ≤ balancedLengthCountInputBits treeCode := by
    exact (natBitLength_mono (Nat.zero_le treeCode)).trans hinput
  have houtput :
      natBitLength (Nat.pair 0 treeCode) ≤
        balancedLengthCountInputBits treeCode :=
    Nat.le_max_right _ _
  rw [show 3 = 2 + 1 by omega]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzero]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair 0 treeCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

def balancedLengthProjectionProgram : NPOracleProgram :=
  [ .unpairLeft 0 0 1
  , .halt 0
  ]

private def balancedLengthProjectionBits (length : ℕ) : ℕ :=
  max (natBitLength (Nat.pair length 0)) (natBitLength length)

private theorem balancedLengthProjectionProgram_oracleFree :
    OracleFree balancedLengthProjectionProgram := by
  rfl

private theorem run_balancedLengthProjectionProgram
    (inputLength length : ℕ) :
    runNPOracleProgram balancedLengthProjectionProgram
        (balancedLengthProjectionBits length) 2
        (initialNPOracleState inputLength (Nat.pair length 0)) =
      some length := by
  have hinput :
      natBitLength (Nat.pair length 0) ≤
        balancedLengthProjectionBits length :=
    Nat.le_max_left _ _
  have hlength :
      natBitLength length ≤ balancedLengthProjectionBits length :=
    Nat.le_max_right _ _
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := length)
    (by rfl) rfl (by simp [initialNPOracleState]) hlength]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hlength

private theorem nonzeroSupportCount_balancedTrueValues
    (values : List ℕ) :
    nonzeroSupportCount (balancedTrueValues values) = values.length := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      change
        nonzeroSupportCount (true :: balancedTrueValues rest) =
          (value :: rest).length
      simp only [nonzeroSupportCount, if_pos, List.length_cons]
      rw [ih, Nat.add_comm]

/-! ## Closed canonical length program -/

def balancedLengthProgram : NPOracleProgram :=
  linkPrograms balancedTrueTreeProgram <|
    linkPrograms balancedLengthCountInputProgram <|
      linkPrograms balancedBoolCountProgram
        balancedLengthProjectionProgram

@[simp] theorem balancedLengthProgram_oracleFree :
    OracleFree balancedLengthProgram := by
  exact oracleFree_linkPrograms balancedTrueTreeProgram_oracleFree <|
    oracleFree_linkPrograms balancedLengthCountInputProgram_oracleFree <|
      oracleFree_linkPrograms balancedBoolCountProgram_oracleFree
        balancedLengthProjectionProgram_oracleFree

def balancedLengthBits (inputLength : ℕ) (values : List ℕ) : ℕ :=
  let trueValues := balancedTrueValues values
  let trueTree := encodeBoolList trueValues
  let length := values.length
  max (balancedTrueTreeBits inputLength values) <|
    max (balancedLengthCountInputBits trueTree) <|
      max (balancedBoolCountBits inputLength 0 trueValues)
        (balancedLengthProjectionBits length)

def balancedLengthFuel (values : List ℕ) : ℕ :=
  linkFuel
    (linkPrograms balancedLengthCountInputProgram <|
      linkPrograms balancedBoolCountProgram
        balancedLengthProjectionProgram)
    (balancedTrueTreeFuel values) <|
      linkFuel
        (linkPrograms balancedBoolCountProgram
          balancedLengthProjectionProgram)
        3 <|
          linkFuel balancedLengthProjectionProgram
            (balancedBoolCountFuel (balancedTrueValues values)) 2

theorem run_balancedLengthProgram
    (inputLength : ℕ) (values : List ℕ) :
    runNPOracleProgram balancedLengthProgram
        (balancedLengthBits inputLength values)
        (balancedLengthFuel values)
        (initialNPOracleState inputLength (encodeBalancedList values)) =
      some values.length := by
  let trueValues := balancedTrueValues values
  let trueTree := encodeBoolList trueValues
  let length := values.length
  let maximumBits := balancedLengthBits inputLength values
  have htrueBits :
      balancedTrueTreeBits inputLength values ≤ maximumBits := by
    simp [maximumBits, balancedLengthBits]
  have hinputBits :
      balancedLengthCountInputBits trueTree ≤ maximumBits := by
    simp [maximumBits, balancedLengthBits, trueTree, trueValues]
  have hcountBits :
      balancedBoolCountBits inputLength 0 trueValues ≤ maximumBits := by
    simp [maximumBits, balancedLengthBits, trueValues]
  have hprojectionBits :
      balancedLengthProjectionBits length ≤ maximumBits := by
    simp [maximumBits, balancedLengthBits, length]
  have hlengthBits : natBitLength inputLength ≤ maximumBits := by
    apply (show natBitLength inputLength ≤
      balancedTrueTreeBits inputLength values from ?_).trans htrueBits
    exact Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlengthBits
  have htrue :
      runNPOracleProgram balancedTrueTreeProgram maximumBits
          (balancedTrueTreeFuel values)
          (initialNPOracleState inputLength (encodeBalancedList values)) =
        some trueTree := by
    exact run_bits_mono
      (run_balancedTrueTreeProgram inputLength values) htrueBits
  have hinput :
      runNPOracleProgram balancedLengthCountInputProgram maximumBits 3
          (initialNPOracleState inputLength trueTree) =
        some (Nat.pair 0 trueTree) := by
    exact run_bits_mono
      (run_balancedLengthCountInputProgram inputLength trueTree) hinputBits
  have hcount :
      runNPOracleProgram balancedBoolCountProgram maximumBits
          (balancedBoolCountFuel trueValues)
          (initialNPOracleState inputLength (Nat.pair 0 trueTree)) =
        some (Nat.pair length 0) := by
    have hrun :=
      run_bits_mono
        (run_balancedBoolCountProgram inputLength 0 trueValues)
        hcountBits
    simpa [trueTree, length, balancedBoolCountOutput,
      nonzeroSupportCount_balancedTrueValues, trueValues] using hrun
  have hprojection :
      runNPOracleProgram balancedLengthProjectionProgram maximumBits 2
          (initialNPOracleState inputLength (Nat.pair length 0)) =
        some length := by
    exact run_bits_mono
      (run_balancedLengthProjectionProgram inputLength length)
      hprojectionBits
  have hcountProjection :
      runNPOracleProgram
          (linkPrograms balancedBoolCountProgram
            balancedLengthProjectionProgram)
          maximumBits
          (linkFuel balancedLengthProjectionProgram
            (balancedBoolCountFuel trueValues) 2)
          (initialNPOracleState inputLength (Nat.pair 0 trueTree)) =
        some length :=
    run_linkPrograms hpositive hlengthBits hcount hprojection
  have htail :
      runNPOracleProgram
          (linkPrograms balancedLengthCountInputProgram <|
            linkPrograms balancedBoolCountProgram
              balancedLengthProjectionProgram)
          maximumBits
          (linkFuel
            (linkPrograms balancedBoolCountProgram
              balancedLengthProjectionProgram)
            3
            (linkFuel balancedLengthProjectionProgram
              (balancedBoolCountFuel trueValues) 2))
          (initialNPOracleState inputLength trueTree) =
        some length :=
    run_linkPrograms hpositive hlengthBits hinput hcountProjection
  have hrun :=
    run_linkPrograms hpositive hlengthBits htrue htail
  simpa [balancedLengthProgram, balancedLengthFuel, trueValues,
    trueTree, length] using hrun

end NearCubicWires.CanonicalBalancedLengthProgram
