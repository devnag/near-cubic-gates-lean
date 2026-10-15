import Proof.MachineModel.CanonicalBinaryArithmeticProgram
import Proof.Circuits.CanonicalPairedCall

/-!
# Canonical native-natural equality

Equality reuses the single binary-width comparator in both directions.  The
paired-call adapter retains both requests without another arithmetic loop, and
one fixed gate conjoins the two Boolean results.
-/

namespace NearCubicWires.CanonicalNativeEqualityProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

def nativeNatEqInput (left right : ℕ) : ℕ :=
  Nat.pair left right

private def nativeNatEqCompareInput (left right : ℕ) : ℕ :=
  Nat.pair (nativeNatLeInput left right) (nativeNatLeInput right left)

def nativeNatEqOutput (left right : ℕ) : ℕ :=
  if left = right then 1 else 0

@[simp] theorem nativeNatEqOutput_ne_zero_iff (left right : ℕ) :
    nativeNatEqOutput left right ≠ 0 ↔ left = right := by
  simp [nativeNatEqOutput]

private def nativeNatEqGateOutput (leftFlag rightFlag : ℕ) : ℕ :=
  if leftFlag = 0 ∨ rightFlag = 0 then 0 else 1

/-! ## Public pair request to the symmetric comparator -/

def nativeNatEqRequestProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .pair 2 3 4 3
  , .pair 3 2 5 4
  , .pair 4 5 0 5
  , .halt 0
  ]

private def nativeNatEqRequestBits (left right : ℕ) : ℕ :=
  max (natBitLength (nativeNatEqInput left right))
    (natBitLength (nativeNatEqCompareInput left right))

private theorem nativeNatEqRequestProgram_oracleFree :
    OracleFree nativeNatEqRequestProgram := by
  rfl

private theorem run_nativeNatEqRequestProgram
    (inputLength left right : ℕ) :
    runNPOracleProgram nativeNatEqRequestProgram
        (nativeNatEqRequestBits left right) 6
        (initialNPOracleState inputLength (nativeNatEqInput left right)) =
      some (nativeNatEqCompareInput left right) := by
  let input := nativeNatEqInput left right
  let leftRequest := nativeNatLeInput left right
  let rightRequest := nativeNatLeInput right left
  let output := nativeNatEqCompareInput left right
  let maximumBits := nativeNatEqRequestBits left right
  have hinput : natBitLength input ≤ maximumBits := by
    exact Nat.le_max_left _ _
  have houtput : natBitLength output ≤ maximumBits := by
    exact Nat.le_max_right _ _
  have hleft : natBitLength left ≤ maximumBits := by
    exact
      (natBitLength_mono (Nat.left_le_pair left right)).trans hinput
  have hright : natBitLength right ≤ maximumBits := by
    exact
      (natBitLength_mono (Nat.right_le_pair left right)).trans hinput
  have hleftRequest : natBitLength leftRequest ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.left_le_pair leftRequest rightRequest)).trans houtput
  have hrightRequest : natBitLength rightRequest ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.right_le_pair leftRequest rightRequest)).trans houtput
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := nativeNatEqRequestProgram)
    (maximumBits := maximumBits) (fuel := 5)
    (pc := 0) (source := 0) (destination := 2) (next := 1)
    (value := left) (by rfl) (by rfl)
    (by simp [initialNPOracleState, nativeNatEqInput]) hleft]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := nativeNatEqRequestProgram)
    (maximumBits := maximumBits) (fuel := 4)
    (pc := 1) (source := 0) (destination := 3) (next := 2)
    (value := right) (by rfl) (by rfl)
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump, nativeNatEqInput]) hright]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction
    (program := nativeNatEqRequestProgram)
    (maximumBits := maximumBits) (fuel := 3)
    (pc := 2) (left := 2) (right := 3) (destination := 4) (next := 3)
    (value := leftRequest) (by rfl) (by rfl)
    (by simp [NPOracleState.write, NPOracleState.jump,
      leftRequest, nativeNatLeInput]) hleftRequest]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction
    (program := nativeNatEqRequestProgram)
    (maximumBits := maximumBits) (fuel := 2)
    (pc := 3) (left := 3) (right := 2) (destination := 5) (next := 4)
    (value := rightRequest) (by rfl) (by rfl)
    (by simp [NPOracleState.write, NPOracleState.jump,
      rightRequest, nativeNatLeInput]) hrightRequest]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (program := nativeNatEqRequestProgram)
    (maximumBits := maximumBits) (fuel := 1)
    (pc := 4) (left := 4) (right := 5) (destination := 0) (next := 5)
    (value := output) (by rfl) (by rfl)
    (by simp [NPOracleState.write, NPOracleState.jump, output,
      leftRequest, rightRequest, nativeNatEqCompareInput]) houtput]
  exact run_halt_instruction
    (program := nativeNatEqRequestProgram)
    (maximumBits := maximumBits) (fuel := 0)
    (pc := 5) (outputRegister := 0) (value := output)
    (by rfl) (by rfl)
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

def nativeNatEqGateProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .branchZero 2 5 2
  , .unpairRight 0 3 3
  , .branchZero 3 5 4
  , .set 0 1 6
  , .set 0 0 6
  , .halt 0
  ]

private def nativeNatEqGateBits (leftFlag rightFlag : ℕ) : ℕ :=
  max (natBitLength (Nat.pair leftFlag rightFlag)) 1

private theorem nativeNatEqGateProgram_oracleFree :
    OracleFree nativeNatEqGateProgram := by
  rfl

private theorem run_nativeNatEqGateProgram
    (inputLength leftFlag rightFlag : ℕ) :
    runNPOracleProgram nativeNatEqGateProgram
        (nativeNatEqGateBits leftFlag rightFlag) 6
        (initialNPOracleState inputLength
          (Nat.pair leftFlag rightFlag)) =
      some (nativeNatEqGateOutput leftFlag rightFlag) := by
  have hinput :
      natBitLength (Nat.pair leftFlag rightFlag) ≤
        nativeNatEqGateBits leftFlag rightFlag :=
    Nat.le_max_left _ _
  have hleft :
      natBitLength leftFlag ≤ nativeNatEqGateBits leftFlag rightFlag :=
    (natBitLength_mono
      (Nat.left_le_pair leftFlag rightFlag)).trans hinput
  have hright :
      natBitLength rightFlag ≤ nativeNatEqGateBits leftFlag rightFlag :=
    (natBitLength_mono
      (Nat.right_le_pair leftFlag rightFlag)).trans hinput
  have hone : natBitLength 1 ≤ nativeNatEqGateBits leftFlag rightFlag := by
    unfold nativeNatEqGateBits
    simp [natBitLength]
  have hzero : natBitLength 0 ≤ nativeNatEqGateBits leftFlag rightFlag := by
    exact (show natBitLength 0 ≤ 1 by simp [natBitLength]).trans
      (Nat.le_max_right _ _)
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := nativeNatEqGateProgram)
    (maximumBits := nativeNatEqGateBits leftFlag rightFlag)
    (fuel := 5) (pc := 0) (source := 0) (destination := 2)
    (next := 1) (value := leftFlag)
    (by rfl) (by rfl)
    (by simp [initialNPOracleState]) hleft]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_branchZero_instruction
    (program := nativeNatEqGateProgram)
    (maximumBits := nativeNatEqGateBits leftFlag rightFlag)
    (fuel := 4) (pc := 1) (register := 2)
    (zeroTarget := 5) (nonzeroTarget := 2)
    (by rfl) (by rfl)]
  by_cases hleftZero : leftFlag = 0
  · rw [if_pos (by simpa using hleftZero)]
    rw [show (4 : ℕ) = 3 + 1 by omega]
    rw [run_set_instruction
      (program := nativeNatEqGateProgram)
      (maximumBits := nativeNatEqGateBits leftFlag rightFlag)
      (fuel := 3) (pc := 5) (register := 0) (value := 0)
      (next := 6) (by rfl) (by rfl) hzero]
    rw [show nativeNatEqGateOutput leftFlag rightFlag = 0 by
      simp [nativeNatEqGateOutput, hleftZero]]
    exact run_halt_instruction
      (program := nativeNatEqGateProgram)
      (maximumBits := nativeNatEqGateBits leftFlag rightFlag)
      (fuel := 2) (pc := 6) (outputRegister := 0) (value := 0)
      (by rfl) (by rfl) (by simp) hzero
  · rw [if_neg (by simpa using hleftZero)]
    rw [show (4 : ℕ) = 3 + 1 by omega]
    rw [run_unpairRight_instruction
      (program := nativeNatEqGateProgram)
      (maximumBits := nativeNatEqGateBits leftFlag rightFlag)
      (fuel := 3) (pc := 2) (source := 0) (destination := 3)
      (next := 3) (value := rightFlag)
      (by rfl) (by rfl)
      (by simp [initialNPOracleState]) hright]
    rw [show (3 : ℕ) = 2 + 1 by omega]
    rw [run_branchZero_instruction
      (program := nativeNatEqGateProgram)
      (maximumBits := nativeNatEqGateBits leftFlag rightFlag)
      (fuel := 2) (pc := 3) (register := 3)
      (zeroTarget := 5) (nonzeroTarget := 4)
      (by rfl) (by rfl)]
    by_cases hrightZero : rightFlag = 0
    · rw [if_pos (by simpa using hrightZero)]
      rw [show (2 : ℕ) = 1 + 1 by omega]
      rw [run_set_instruction
        (program := nativeNatEqGateProgram)
        (maximumBits := nativeNatEqGateBits leftFlag rightFlag)
        (fuel := 1) (pc := 5) (register := 0) (value := 0)
        (next := 6) (by rfl) (by rfl) hzero]
      rw [show nativeNatEqGateOutput leftFlag rightFlag = 0 by
        simp [nativeNatEqGateOutput, hrightZero]]
      exact run_halt_instruction
        (program := nativeNatEqGateProgram)
        (maximumBits := nativeNatEqGateBits leftFlag rightFlag)
        (fuel := 0) (pc := 6) (outputRegister := 0) (value := 0)
        (by rfl) (by rfl) (by simp) hzero
    · rw [if_neg (by simpa using hrightZero)]
      rw [show (2 : ℕ) = 1 + 1 by omega]
      rw [run_set_instruction
        (program := nativeNatEqGateProgram)
        (maximumBits := nativeNatEqGateBits leftFlag rightFlag)
        (fuel := 1) (pc := 4) (register := 0) (value := 1)
        (next := 6) (by rfl) (by rfl) hone]
      rw [show nativeNatEqGateOutput leftFlag rightFlag = 1 by
        simp [nativeNatEqGateOutput, hleftZero, hrightZero]]
      exact run_halt_instruction
        (program := nativeNatEqGateProgram)
        (maximumBits := nativeNatEqGateBits leftFlag rightFlag)
        (fuel := 0) (pc := 6) (outputRegister := 0) (value := 1)
        (by rfl) (by rfl) (by simp) hone

def nativeNatEqCompareProgram : NPOracleProgram :=
  pairedCallProgram nativeNatLeProgram

def nativeNatEqCompareFuel (left right : ℕ) : ℕ :=
  pairedCallFuel nativeNatLeProgram
    (nativeNatLeFuel left right) (nativeNatLeFuel right left)

private def nativeNatEqCompareBits
    (inputLength left right : ℕ) : ℕ :=
  pairedCallBits inputLength
    (nativeNatLeBits left right) (nativeNatLeBits right left)
    (nativeNatLeInput left right) (nativeNatLeInput right left)
    (nativeNatLeOutput left right) (nativeNatLeOutput right left)

private theorem nativeNatEqCompareProgram_oracleFree :
    OracleFree nativeNatEqCompareProgram := by
  exact pairedCallProgram_oracleFree nativeNatLeProgram
    nativeNatLeProgram_oracleFree

private theorem run_nativeNatEqCompareProgram
    (inputLength left right : ℕ) :
    runNPOracleProgram nativeNatEqCompareProgram
        (nativeNatEqCompareBits inputLength left right)
        (nativeNatEqCompareFuel left right)
        (initialNPOracleState inputLength
          (nativeNatEqCompareInput left right)) =
      some
        (Nat.pair (nativeNatLeOutput left right)
          (nativeNatLeOutput right left)) := by
  exact run_pairedCallProgram nativeNatLeProgram inputLength
    (nativeNatLeBits left right) (nativeNatLeBits right left)
    (nativeNatLeFuel left right) (nativeNatLeFuel right left)
    (nativeNatLeInput left right) (nativeNatLeInput right left)
    (nativeNatLeOutput left right) (nativeNatLeOutput right left)
    (run_nativeNatLeProgram inputLength left right)
    (run_nativeNatLeProgram inputLength right left)

def nativeNatEqCoreProgram : NPOracleProgram :=
  linkPrograms nativeNatEqCompareProgram nativeNatEqGateProgram

private theorem nativeNatEqCoreProgram_oracleFree :
    OracleFree nativeNatEqCoreProgram := by
  exact oracleFree_linkPrograms nativeNatEqCompareProgram_oracleFree
    nativeNatEqGateProgram_oracleFree

def nativeNatEqCoreFuel (left right : ℕ) : ℕ :=
  linkFuel nativeNatEqGateProgram (nativeNatEqCompareFuel left right) 6

private def nativeNatEqCoreBits (inputLength left right : ℕ) : ℕ :=
  max (nativeNatEqCompareBits inputLength left right)
    (nativeNatEqGateBits
      (nativeNatLeOutput left right) (nativeNatLeOutput right left))

private theorem run_nativeNatEqCoreProgram (inputLength left right : ℕ) :
    runNPOracleProgram nativeNatEqCoreProgram
        (nativeNatEqCoreBits inputLength left right)
        (nativeNatEqCoreFuel left right)
        (initialNPOracleState inputLength
          (nativeNatEqCompareInput left right)) =
      some (nativeNatEqOutput left right) := by
  let maximumBits := nativeNatEqCoreBits inputLength left right
  have hcompare :
      nativeNatEqCompareBits inputLength left right ≤ maximumBits :=
    Nat.le_max_left _ _
  have hgate :
      nativeNatEqGateBits
          (nativeNatLeOutput left right) (nativeNatLeOutput right left) ≤
        maximumBits :=
    Nat.le_max_right _ _
  have hlength :
      natBitLength inputLength ≤ maximumBits := by
    have hinCompare :
        natBitLength inputLength ≤
          nativeNatEqCompareBits inputLength left right := by
      unfold nativeNatEqCompareBits pairedCallBits
      exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
    exact hinCompare.trans hcompare
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  apply run_linkPrograms hpositive hlength
  · exact run_bits_mono
      (run_nativeNatEqCompareProgram inputLength left right) hcompare
  · have hrun :=
      run_bits_mono
        (run_nativeNatEqGateProgram inputLength
          (nativeNatLeOutput left right) (nativeNatLeOutput right left))
        hgate
    rw [show nativeNatEqOutput left right =
        nativeNatEqGateOutput
          (nativeNatLeOutput left right)
          (nativeNatLeOutput right left) by
      rw [nativeNatLeOutput_eq, nativeNatLeOutput_eq]
      by_cases heq : left = right
      · subst right
        simp [nativeNatEqOutput, nativeNatEqGateOutput]
      · have hnotBoth : ¬(left ≤ right ∧ right ≤ left) := by
          intro hboth
          exact heq (Nat.le_antisymm hboth.1 hboth.2)
        simp only [nativeNatEqOutput, if_neg heq,
          nativeNatEqGateOutput]
        by_cases hleft : left ≤ right
        · have hright : ¬right ≤ left := by
            intro hright
            exact hnotBoth ⟨hleft, hright⟩
          simp [hleft, hright]
        · simp [hleft]]
    exact hrun

/-- The single binary-width equality program used by canonicality guards.
Its public request is always the universal pair `pair(left, right)`; the
comparator-specific symmetric request remains private plumbing. -/
def nativeNatEqProgram : NPOracleProgram :=
  linkPrograms nativeNatEqRequestProgram nativeNatEqCoreProgram

@[simp] theorem nativeNatEqProgram_oracleFree :
    OracleFree nativeNatEqProgram := by
  exact oracleFree_linkPrograms nativeNatEqRequestProgram_oracleFree
    nativeNatEqCoreProgram_oracleFree

def nativeNatEqFuel (left right : ℕ) : ℕ :=
  linkFuel nativeNatEqCoreProgram 6 (nativeNatEqCoreFuel left right)

def nativeNatEqBits (inputLength left right : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (nativeNatEqRequestBits left right)
      (nativeNatEqCoreBits inputLength left right)

theorem run_nativeNatEqProgram (inputLength left right : ℕ) :
    runNPOracleProgram nativeNatEqProgram
        (nativeNatEqBits inputLength left right)
        (nativeNatEqFuel left right)
        (initialNPOracleState inputLength (nativeNatEqInput left right)) =
      some (nativeNatEqOutput left right) := by
  let maximumBits := nativeNatEqBits inputLength left right
  have hlength : natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hrequest : nativeNatEqRequestBits left right ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hcore :
      nativeNatEqCoreBits inputLength left right ≤ maximumBits :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  apply run_linkPrograms hpositive hlength
  · exact run_bits_mono
      (run_nativeNatEqRequestProgram inputLength left right) hrequest
  · exact run_bits_mono
      (run_nativeNatEqCoreProgram inputLength left right) hcore

end NearCubicWires.CanonicalNativeEqualityProgram
