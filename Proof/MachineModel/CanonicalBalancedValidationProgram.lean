import Proof.MachineModel.BalancedClauseStreamFlattenProgram
import Proof.Circuits.CanonicalBalancedBuilder
import Proof.MachineModel.CanonicalNatDecodeProgram
import Proof.MachineModel.CanonicalNativeEqualityProgram
import Proof.MachineModel.PreserveRightProgram
import Proof.Foundations.VerifiedLinker

/-!
# Executable canonical-balanced validation

The validator normalizes one structural balanced tree with the existing
traversal, stream flattener, and midpoint builder, then compares that unique
normal form with the original code.  The public input is only the candidate
code: duplication, preservation, and equality requests are fixed machine
plumbing rather than caller-supplied evidence.
-/

namespace NearCubicWires.CanonicalBalancedValidationProgram

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

@[simp] theorem treeStreamValues_map_singleton
    (tree : BalancedTraversalTree) :
    treeStreamValues (tree.map singletonTaggedBit) = tree.atoms := by
  unfold treeStreamValues
  rw [BalancedTraversalTree.atoms_map]
  generalize tree.atoms = atoms
  induction atoms with
  | nil => rfl
  | cons atom atoms inductionHypothesis =>
      simp [singletonTaggedBit, inductionHypothesis]

private theorem mappedSingletonStreams_valid
    (tree : BalancedTraversalTree) :
    ∀ atom ∈ (tree.map singletonTaggedBit).atoms,
      encodeTaggedList (streamOfCode atom) = atom := by
  intro atom hmember
  rw [BalancedTraversalTree.atoms_map] at hmember
  rcases List.mem_map.mp hmember with ⟨source, _hsource, rfl⟩
  simp [singletonTaggedBit]

/-! ## Total raw syntax normalization -/

def balancedStructuralNormalizeProgram : NPOracleProgram :=
  balancedTraversalController balancedTraversalLeafReturnPc 34 ++
    [.halt 0]

@[simp] theorem balancedStructuralNormalizeProgram_oracleFree :
    OracleFree balancedStructuralNormalizeProgram := by
  rfl

theorem balancedStructuralNormalizeProgram_controllerAt :
    BalancedTraversalControllerAt balancedStructuralNormalizeProgram
      balancedTraversalLeafReturnPc 34 := by
  intro pc instruction hlookup
  have hpc :
      pc <
        (balancedTraversalController
          balancedTraversalLeafReturnPc 34).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [balancedStructuralNormalizeProgram]
  rw [List.getElem?_append_left hpc]
  exact hlookup

def balancedStructuralNormalizeFuel
    (tree : RawBalancedTraversalTree) : ℕ :=
  rawBalancedTraversalSteps tree + 2

def balancedStructuralNormalizeBits
    (inputLength : ℕ) (tree : RawBalancedTraversalTree) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    rawBalancedTraversalRequiredBits tree []

theorem run_balancedStructuralNormalizeProgram
    (inputLength : ℕ) (tree : RawBalancedTraversalTree)
    (hvalid : tree.Valid) :
    runNPOracleProgram balancedStructuralNormalizeProgram
        (balancedStructuralNormalizeBits inputLength tree)
        (balancedStructuralNormalizeFuel tree)
        (initialNPOracleState inputLength tree.rawCode) =
      some tree.normalized.code := by
  let maximumBits := balancedStructuralNormalizeBits inputLength tree
  let initial := initialNPOracleState inputLength tree.rawCode
  have hfit :
      RawBalancedTraversalFits maximumBits tree [] :=
    (rawBalancedTraversalRequiredBits_le_iff maximumBits tree []).mp
      (by simp [maximumBits, balancedStructuralNormalizeBits])
  rcases run_rawBalancedTraversal_subtree tree [] initial inputLength 9
      (by omega) balancedStructuralNormalizeProgram_controllerAt rfl
      (by rfl)
      (by simp [initial, initialNPOracleState])
      (by simp [initial, initialNPOracleState,
        encodeBalancedTraversalStack, encodeTaggedList])
      (by simp [initial, initialNPOracleState])
      hvalid hfit with
    ⟨atResume, htreeRuns, hatResumePc, hatResumeCurrent,
      hatResumeStack, _hatResumePersistent⟩
  have hfinish :
      runNPOracleProgram balancedStructuralNormalizeProgram
          maximumBits 2 atResume =
        some tree.normalized.code := by
    rw [show (2 : ℕ) = 1 + 1 by omega]
    rw [run_branchZero_instruction
      (program := balancedStructuralNormalizeProgram)
      (maximumBits := maximumBits) (fuel := 1)
      (pc := 15) (register := 2)
      (zeroTarget := 34) (nonzeroTarget := 16)
      (by rfl) hatResumePc]
    rw [show atResume.registers 2 = 0 by
      simpa [encodeBalancedTraversalStack, encodeTaggedList] using
        hatResumeStack]
    rw [if_pos rfl]
    exact run_halt_instruction
      (program := balancedStructuralNormalizeProgram)
      (maximumBits := maximumBits) (fuel := 0)
      (pc := 34) (outputRegister := 0)
      (value := tree.normalized.code)
      (by rfl) (by rfl)
      (by simpa [NPOracleState.jump] using hatResumeCurrent)
      hfit.output
  unfold balancedStructuralNormalizeFuel
  rw [htreeRuns 2]
  exact hfinish

/-! ## One canonicalizer assembled from the shared sequence machinery -/

def balancedCanonicalizeProgram : NPOracleProgram :=
  linkPrograms
    (linkPrograms balancedBitSingletonProgram
      balancedClauseStreamFlattenProgram)
    taggedToBalancedProgram

@[simp] theorem balancedCanonicalizeProgram_oracleFree :
    OracleFree balancedCanonicalizeProgram := by
  exact oracleFree_linkPrograms
    (oracleFree_linkPrograms balancedBitSingletonProgram_oracleFree
      balancedClauseStreamFlattenProgram_oracleFree)
    taggedToBalancedProgram_oracleFree

def balancedCanonicalizeFuel
    (tree : BalancedTraversalTree) : ℕ :=
  linkFuel taggedToBalancedProgram
    (linkFuel balancedClauseStreamFlattenProgram
      (balancedBitSingletonTreeFuel tree)
      (balancedTreeStreamFlattenFuel
        (tree.map singletonTaggedBit)))
    (taggedToBalancedFuel tree.atoms)

def balancedCanonicalizeBits
    (inputLength : ℕ) (tree : BalancedTraversalTree) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (balancedBitSingletonTreeBits tree) <|
      max
        (balancedTreeStreamFlattenMaximumBits
          (tree.map singletonTaggedBit))
        (taggedToBalancedRegisterBitsFor inputLength tree.atoms)

theorem run_balancedCanonicalizeProgram
    (inputLength : ℕ) (tree : BalancedTraversalTree) :
    runNPOracleProgram balancedCanonicalizeProgram
        (balancedCanonicalizeBits inputLength tree)
        (balancedCanonicalizeFuel tree)
        (initialNPOracleState inputLength tree.code) =
      some (encodeBalancedList tree.atoms) := by
  let maximumBits := balancedCanonicalizeBits inputLength tree
  let mapped := tree.map singletonTaggedBit
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, balancedCanonicalizeBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, balancedCanonicalizeBits]
  have hsingleton :
      balancedBitSingletonTreeBits tree ≤ maximumBits := by
    simp [maximumBits, balancedCanonicalizeBits]
  have hflatten :
      balancedTreeStreamFlattenMaximumBits mapped ≤ maximumBits := by
    simp [maximumBits, balancedCanonicalizeBits, mapped]
  have hbuilder :
      taggedToBalancedRegisterBitsFor inputLength tree.atoms ≤
        maximumBits := by
    simp [maximumBits, balancedCanonicalizeBits]
  have hfirst :
      runNPOracleProgram balancedBitSingletonProgram maximumBits
          (balancedBitSingletonTreeFuel tree)
          (initialNPOracleState inputLength tree.code) =
        some mapped.code := by
    exact run_bits_mono
      (run_balancedBitSingletonTreeProgram inputLength tree) hsingleton
  have hsecond :
      runNPOracleProgram balancedClauseStreamFlattenProgram maximumBits
          (balancedTreeStreamFlattenFuel mapped)
          (initialNPOracleState inputLength mapped.code) =
        some (encodeTaggedList tree.atoms) := by
    have hrun :=
      run_bits_mono
        (run_balancedClauseStreamFlattenTree mapped inputLength
          (mappedSingletonStreams_valid tree))
        hflatten
    simpa [mapped] using hrun
  have hthird :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (taggedToBalancedFuel tree.atoms)
          (initialNPOracleState inputLength
            (encodeTaggedList tree.atoms)) =
        some (encodeBalancedList tree.atoms) := by
    exact run_bits_mono
      (run_taggedToBalancedProgram_from inputLength tree.atoms) hbuilder
  apply run_linkPrograms hpositive hlength
  · apply run_linkPrograms hpositive hlength hfirst hsecond
  · exact hthird

/-! The raw front door is linked exactly once before canonical midpoint
rebuilding.  No downstream consumer may bypass this normalization seam. -/

def balancedRawCanonicalizeProgram : NPOracleProgram :=
  linkPrograms balancedStructuralNormalizeProgram
    balancedCanonicalizeProgram

@[simp] theorem balancedRawCanonicalizeProgram_oracleFree :
    OracleFree balancedRawCanonicalizeProgram := by
  exact oracleFree_linkPrograms
    balancedStructuralNormalizeProgram_oracleFree
    balancedCanonicalizeProgram_oracleFree

def balancedRawCanonicalizeFuel
    (tree : RawBalancedTraversalTree) : ℕ :=
  linkFuel balancedCanonicalizeProgram
    (balancedStructuralNormalizeFuel tree)
    (balancedCanonicalizeFuel tree.normalized)

def balancedRawCanonicalizeBits
    (inputLength : ℕ) (tree : RawBalancedTraversalTree) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (balancedStructuralNormalizeBits inputLength tree)
      (balancedCanonicalizeBits inputLength tree.normalized)

theorem run_balancedRawCanonicalizeProgram
    (inputLength : ℕ) (tree : RawBalancedTraversalTree)
    (hvalid : tree.Valid) :
    runNPOracleProgram balancedRawCanonicalizeProgram
        (balancedRawCanonicalizeBits inputLength tree)
        (balancedRawCanonicalizeFuel tree)
        (initialNPOracleState inputLength tree.rawCode) =
      some (encodeBalancedList tree.atoms) := by
  let maximumBits := balancedRawCanonicalizeBits inputLength tree
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, balancedRawCanonicalizeBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, balancedRawCanonicalizeBits]
  have hnormalize :
      balancedStructuralNormalizeBits inputLength tree ≤ maximumBits := by
    simp [maximumBits, balancedRawCanonicalizeBits]
  have hcanonicalize :
      balancedCanonicalizeBits inputLength tree.normalized ≤
        maximumBits := by
    simp [maximumBits, balancedRawCanonicalizeBits]
  apply run_linkPrograms hpositive hlength
  · exact run_bits_mono
      (run_balancedStructuralNormalizeProgram inputLength tree hvalid)
      hnormalize
  · simpa [RawBalancedTraversalTree.atoms] using
      run_bits_mono
        (run_balancedCanonicalizeProgram inputLength tree.normalized)
        hcanonicalize

/-- Total public normalization: arbitrary raw words are traversed through the
unique proof view before rebuilding the canonical balanced encoding. -/
theorem run_balancedRawCanonicalizeProgram_total
    (inputLength raw : ℕ) :
    runNPOracleProgram balancedRawCanonicalizeProgram
        (balancedRawCanonicalizeBits inputLength
          (rawBalancedTraversalTree raw))
        (balancedRawCanonicalizeFuel
          (rawBalancedTraversalTree raw))
        (initialNPOracleState inputLength raw) =
      some
        (encodeBalancedList
          (rawBalancedTraversalTree raw).atoms) := by
  have hrun :=
    run_balancedRawCanonicalizeProgram inputLength
      (rawBalancedTraversalTree raw)
      (rawBalancedTraversalTree_valid raw)
  simpa [rawBalancedTraversalTree_rawCode] using hrun

/-! ## Retain the untrusted code for the final equality guard -/

def duplicateNatProgram : NPOracleProgram :=
  [ .pair 0 0 0 1
  , .halt 0
  ]

private def duplicateNatBits (value : ℕ) : ℕ :=
  max (natBitLength value) (natBitLength (Nat.pair value value))

private theorem duplicateNatProgram_oracleFree :
    OracleFree duplicateNatProgram := by
  rfl

private theorem run_duplicateNatProgram
    (inputLength value : ℕ) :
    runNPOracleProgram duplicateNatProgram (duplicateNatBits value) 2
        (initialNPOracleState inputLength value) =
      some (Nat.pair value value) := by
  have houtput :
      natBitLength (Nat.pair value value) ≤ duplicateNatBits value :=
    Nat.le_max_right _ _
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (program := duplicateNatProgram)
    (maximumBits := duplicateNatBits value) (fuel := 1)
    (pc := 0) (left := 0) (right := 0) (destination := 0) (next := 1)
    (value := Nat.pair value value)
    (by rfl) (by rfl) (by simp [initialNPOracleState]) houtput]
  exact run_halt_instruction
    (program := duplicateNatProgram)
    (maximumBits := duplicateNatBits value) (fuel := 0)
    (pc := 1) (outputRegister := 0) (value := Nat.pair value value)
    (by rfl) (by rfl)
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

def balancedCanonicalityPrepareProgram : NPOracleProgram :=
  linkPrograms duplicateNatProgram <|
    preserveRightProgram balancedRawCanonicalizeProgram

private theorem balancedCanonicalityPrepareProgram_oracleFree :
    OracleFree balancedCanonicalityPrepareProgram := by
  exact oracleFree_linkPrograms duplicateNatProgram_oracleFree <|
    preserveRightProgram_oracleFree balancedRawCanonicalizeProgram
      balancedRawCanonicalizeProgram_oracleFree

def balancedCanonicalityPrepareFuel
    (tree : RawBalancedTraversalTree) : ℕ :=
  linkFuel (preserveRightProgram balancedRawCanonicalizeProgram) 2 <|
    preserveRightFuel (balancedRawCanonicalizeFuel tree)

private def balancedCanonicalityPrepareBits
    (inputLength : ℕ) (tree : RawBalancedTraversalTree) : ℕ :=
  let rebuilt := encodeBalancedList tree.atoms
  max 1 <| max (natBitLength inputLength) <|
    max (duplicateNatBits tree.rawCode) <|
      preserveRightBits
        (balancedRawCanonicalizeBits inputLength tree)
        tree.rawCode tree.rawCode rebuilt

private theorem run_balancedCanonicalityPrepareProgram
    (inputLength : ℕ) (tree : RawBalancedTraversalTree)
    (hvalid : tree.Valid) :
    runNPOracleProgram balancedCanonicalityPrepareProgram
        (balancedCanonicalityPrepareBits inputLength tree)
        (balancedCanonicalityPrepareFuel tree)
        (initialNPOracleState inputLength tree.rawCode) =
      some
        (nativeNatEqInput
          (encodeBalancedList tree.atoms) tree.rawCode) := by
  let rebuilt := encodeBalancedList tree.atoms
  let maximumBits := balancedCanonicalityPrepareBits inputLength tree
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, balancedCanonicalityPrepareBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, balancedCanonicalityPrepareBits]
  have hduplicate : duplicateNatBits tree.rawCode ≤ maximumBits := by
    simp [maximumBits, balancedCanonicalityPrepareBits]
  have hpreserve :
      preserveRightBits
          (balancedRawCanonicalizeBits inputLength tree)
          tree.rawCode tree.rawCode rebuilt ≤ maximumBits := by
    simp [maximumBits, balancedCanonicalityPrepareBits, rebuilt]
  apply run_linkPrograms hpositive hlength
  · exact run_bits_mono
      (run_duplicateNatProgram inputLength tree.rawCode) hduplicate
  · have hrun :=
      run_preserveRightProgram balancedRawCanonicalizeProgram inputLength
        (balancedRawCanonicalizeBits inputLength tree)
        (balancedRawCanonicalizeFuel tree)
        tree.rawCode tree.rawCode rebuilt
        (run_balancedRawCanonicalizeProgram inputLength tree hvalid)
    simpa [nativeNatEqInput, rebuilt] using run_bits_mono hrun hpreserve

/-! ## Public Boolean canonicality result -/

def balancedCanonicalityProgram : NPOracleProgram :=
  linkPrograms balancedCanonicalityPrepareProgram nativeNatEqProgram

@[simp] theorem balancedCanonicalityProgram_oracleFree :
    OracleFree balancedCanonicalityProgram := by
  exact oracleFree_linkPrograms
    balancedCanonicalityPrepareProgram_oracleFree
    nativeNatEqProgram_oracleFree

def balancedCanonicalityTreeFuel
    (tree : RawBalancedTraversalTree) : ℕ :=
  linkFuel nativeNatEqProgram
    (balancedCanonicalityPrepareFuel tree)
    (nativeNatEqFuel (encodeBalancedList tree.atoms) tree.rawCode)

private def balancedCanonicalityTreeBits
    (inputLength : ℕ) (tree : RawBalancedTraversalTree) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (balancedCanonicalityPrepareBits inputLength tree)
      (nativeNatEqBits inputLength
        (encodeBalancedList tree.atoms) tree.rawCode)

def balancedCanonicalityOutput (raw : ℕ) : ℕ :=
  let tree := rawBalancedTraversalTree raw
  if encodeBalancedList tree.atoms = raw then 1 else 0

private theorem nativeNatEqOutput_rebalanced
    (tree : RawBalancedTraversalTree) (hvalid : tree.Valid) :
    nativeNatEqOutput (encodeBalancedList tree.atoms) tree.rawCode =
      balancedCanonicalityOutput tree.rawCode := by
  unfold balancedCanonicalityOutput
  rw [rawBalancedTraversalTree_of_valid tree hvalid]
  rfl

private theorem run_balancedCanonicalityProgram_tree
    (inputLength : ℕ) (tree : RawBalancedTraversalTree)
    (hvalid : tree.Valid) :
    runNPOracleProgram balancedCanonicalityProgram
        (balancedCanonicalityTreeBits inputLength tree)
        (balancedCanonicalityTreeFuel tree)
        (initialNPOracleState inputLength tree.rawCode) =
      some (balancedCanonicalityOutput tree.rawCode) := by
  let maximumBits := balancedCanonicalityTreeBits inputLength tree
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, balancedCanonicalityTreeBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, balancedCanonicalityTreeBits]
  have hprepare :
      balancedCanonicalityPrepareBits inputLength tree ≤ maximumBits := by
    simp [maximumBits, balancedCanonicalityTreeBits]
  have hequality :
      nativeNatEqBits inputLength
          (encodeBalancedList tree.atoms) tree.rawCode ≤ maximumBits := by
    simp [maximumBits, balancedCanonicalityTreeBits]
  apply run_linkPrograms hpositive hlength
  · exact run_bits_mono
      (run_balancedCanonicalityPrepareProgram inputLength tree hvalid)
      hprepare
  · rw [← nativeNatEqOutput_rebalanced tree hvalid]
    exact run_bits_mono
      (run_nativeNatEqProgram inputLength
        (encodeBalancedList tree.atoms) tree.rawCode)
      hequality

/-- Exact public budgets are computed from the raw code's total proof view;
neither a shape witness nor a recursion limit is supplied by the caller. -/
def balancedCanonicalityFuel (raw : ℕ) : ℕ :=
  balancedCanonicalityTreeFuel (rawBalancedTraversalTree raw)

def balancedCanonicalityBits (inputLength raw : ℕ) : ℕ :=
  balancedCanonicalityTreeBits inputLength (rawBalancedTraversalTree raw)

theorem run_balancedCanonicalityProgram
    (inputLength raw : ℕ) :
    runNPOracleProgram balancedCanonicalityProgram
        (balancedCanonicalityBits inputLength raw)
        (balancedCanonicalityFuel raw)
        (initialNPOracleState inputLength raw) =
      some (balancedCanonicalityOutput raw) := by
  let tree := rawBalancedTraversalTree raw
  have hvalid : tree.Valid := rawBalancedTraversalTree_valid raw
  have hcode : tree.rawCode = raw :=
    rawBalancedTraversalTree_rawCode raw
  simpa [balancedCanonicalityBits, balancedCanonicalityFuel, tree,
    hcode] using
      run_balancedCanonicalityProgram_tree inputLength tree hvalid

/-- The executable equality guard is extensionally the public decoder:
canonical values are accepted, while every malformed tag or alternate shape
is rejected. -/
theorem balancedCanonicalityOutput_eq_one_iff (raw : ℕ) :
    balancedCanonicalityOutput raw = 1 ↔
      (decodeBalancedList raw).isSome := by
  let tree := rawBalancedTraversalTree raw
  constructor
  · intro haccepts
    have hcanonical : encodeBalancedList tree.atoms = raw := by
      simpa [balancedCanonicalityOutput, tree] using haccepts
    rw [← hcanonical, decodeBalancedList_encode]
    rfl
  · intro hdecode
    cases hdecoded : decodeBalancedList raw with
    | none =>
        simp [hdecoded] at hdecode
    | some values =>
        have hraw : encodeBalancedList values = raw :=
          encodeBalancedList_of_decode hdecoded
        have hnormalized :
            tree.normalized = balancedTraversalTree values := by
          dsimp [tree]
          rw [← hraw, ← balancedTraversalTree_code]
          exact rawBalancedTraversalTree_normalized_code
            (balancedTraversalTree values)
        have hatoms : tree.atoms = values := by
          rw [RawBalancedTraversalTree.atoms, hnormalized,
            balancedTraversalTree_atoms]
        simp [balancedCanonicalityOutput, tree, hatoms, hraw]

theorem balancedCanonicalityOutput_eq_zero_iff (raw : ℕ) :
    balancedCanonicalityOutput raw = 0 ↔
      decodeBalancedList raw = none := by
  constructor
  · intro hzero
    cases hdecode : decodeBalancedList raw with
    | none => rfl
    | some values =>
        have hisSome : (decodeBalancedList raw).isSome := by
          simp [hdecode]
        have hone :=
          (balancedCanonicalityOutput_eq_one_iff raw).2 hisSome
        omega
  · intro hdecode
    have hnotOne : balancedCanonicalityOutput raw ≠ 1 := by
      intro hone
      have hisSome :=
        (balancedCanonicalityOutput_eq_one_iff raw).1 hone
      simp [hdecode] at hisSome
    unfold balancedCanonicalityOutput
    dsimp only
    split
    · rename_i hcanonical
      exact False.elim <| hnotOne <| by
        simp [balancedCanonicalityOutput, hcanonical]
    · rfl

end NearCubicWires.CanonicalBalancedValidationProgram
