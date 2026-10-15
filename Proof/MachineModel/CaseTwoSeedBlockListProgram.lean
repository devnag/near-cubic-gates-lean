import Proof.CaseAnalysis.CaseTwoTargetLanguageClosure
import Proof.MachineModel.RuntimeLeftShiftProgram

/-!
# The Case-2 seed block list, from the requested point code

`CaseTwoTargetLanguageClosure` leaves exactly one stage of the Case-2 branch as
a hypothesis: the loop that evaluates the scheduled Case-2 seed once per XOR
copy and hands the resulting block list to the fixed target-bit dispatcher.
This module builds that loop.

The construction is the same one `OuterProofRecoveryFormulaSeedProgram` uses
for the C.12 clause stream: `GeneratedBalancedRangeProgram` materializes the
`copies` request atoms directly in the canonical balanced representation, and
`CanonicalBalancedCall` runs one callee per atom.  Two straight-line framing
adapters bracket the pair — one building the range request from the requested
point code, one attaching the Case-2 dispatch tag — and one more drops the
context the range generator retains.

Two mathematical bridges make the result usable.

* `bitSlice_encodeBitInput_blockInput` identifies the interior digit window of
  the requested point code at offset `block * arity` with the code of that
  block's own restriction, so the per-block callee never needs the whole point.
* `xorPower_eq_foldl_range` replaces the choice-selected enumeration
  `Finset.univ.toList` inside `xorPower` by the machine's own `List.range`
  order.  Both lists enumerate `Fin copies` without repetition, and the parity
  fold is invariant under permutation.

The single remaining parameter is the per-block occurrence callee: one program
receiving `pair block pointCode` at the public target length and returning the
honest occurrence bit of the published factory at that block's occurrence code.
`CaseTwoOccurrenceProgram.run_caseTwoOccurrenceProgram` already executes the
occurrence itself; what the callee still has to add in front of it is the
occurrence-code assembly, whose only non-straight-line ingredient — scaling by
a run-time power of two — is `RuntimeLeftShiftProgram`.
-/

namespace NearCubicWires.CaseTwoSeedBlockListProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSliceProgram
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceCoordinates
open NearCubicWires.CaseTwoOccurrenceEvaluation
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoOccurrenceSpecification
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoTargetLanguageClosure
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The parity fold does not see the enumeration order -/

private instance : RightCommutative (xor : Bool → Bool → Bool) :=
  ⟨by decide⟩

/-- The choice-selected enumeration of `Fin copies` and the machine's own
`List.range` order agree up to permutation. -/
private theorem univList_perm_finRange (copies : ℕ) :
    ((Finset.univ : Finset (Fin copies)).toList).Perm (List.finRange copies) :=
  (List.perm_ext_iff_of_nodup (Finset.nodup_toList _)
      (List.nodup_finRange copies)).mpr (by intro block; simp)

/-- **The XOR power in machine order.**  `xorPower` folds the seed over the
choice-selected enumeration of `Fin copies`; any nat-indexed family agreeing
with it blockwise folds to the same parity over `List.range copies`. -/
theorem xorPower_eq_foldl_range {arity copies : ℕ} (seed : BoolFunction arity)
    (point : BitInput (copies * arity)) (value : ℕ → Bool)
    (hvalue : ∀ block : Fin copies,
      value block.val = seed (blockInput point block)) :
    (((List.range copies).map value).foldl xor false) =
      xorPower seed copies point := by
  have hrange :
      (List.range copies).map value =
        (List.finRange copies).map fun block : Fin copies =>
          seed (blockInput point block) := by
    rw [← List.map_coe_finRange_eq_range, List.map_map]
    exact List.map_congr_left fun block _ => hvalue block
  have hperm :
      ((List.finRange copies).map fun block : Fin copies =>
          seed (blockInput point block)).Perm
        (((Finset.univ : Finset (Fin copies)).toList).map
          fun block : Fin copies => seed (blockInput point block)) :=
    ((univList_perm_finRange copies).map _).symm
  rw [hrange, hperm.foldl_eq false, xorPower, List.foldl_map]

/-! ## 2. One block of the requested point is one digit window -/

/-- **The block window.**  Reading the requested point as one natural code, the
`block`-th arity-wide window is exactly the code of that block's restriction.
No block therefore needs more than one `bitSlice` of the request. -/
theorem bitSlice_encodeBitInput_blockInput
    {arity copies target : ℕ} (point : BitInput target)
    (hle : copies * arity ≤ target) (block : Fin copies) :
    bitSlice (block.val * arity) arity (encodeBitInput point) =
      encodeBitInput
        (blockInput
          (fun index : Fin (copies * arity) =>
            point ⟨index.val, index.isLt.trans_le hle⟩)
          block) := by
  have hwindow :
      (fun bit : Fin arity =>
          (bitSlice (block.val * arity) arity
            (encodeBitInput point)).testBit bit.val) =
        blockInput
          (fun index : Fin (copies * arity) =>
            point ⟨index.val, index.isLt.trans_le hle⟩)
          block := by
    funext bit
    have hindex : block.val * arity + bit.val < target := by
      have hstep : block.val * arity + bit.val < copies * arity := by
        have hbound : block.val * arity + arity ≤ copies * arity := by
          rw [← Nat.succ_mul]
          exact Nat.mul_le_mul_right arity (Nat.succ_le_of_lt block.isLt)
        omega
      omega
    have hslice :
        (bitSlice (block.val * arity) arity
            (encodeBitInput point)).testBit bit.val =
          (encodeBitInput point).testBit (block.val * arity + bit.val) := by
      rw [bitSlice, Nat.testBit_mod_two_pow]
      simp [bit.isLt, Nat.testBit_shiftRight]
    rw [hslice, encodeBitInput_eq_ofBits]
    exact Nat.testBit_ofBits_lt point (block.val * arity + bit.val) hindex
  rw [← hwindow]
  exact
    (encodeBitInput_testBit
      (bitSlice_lt (block.val * arity) arity (encodeBitInput point))).symm

/-! ## 3. The per-block occurrence value -/

/-- The occurrence code of one block of the requested point, in the native
occurrence ABI of `CaseTwoOccurrenceProgram`. -/
def caseTwoBlockOccurrenceCode
    (nativeInputBits paddedInputBits nativeClauseBits paddedClauseBits
      arity pointCode block : ℕ) : ℕ :=
  nativeOccurrenceCode nativeInputBits paddedInputBits nativeClauseBits
    paddedClauseBits (bitSlice (block * arity) arity pointCode)

/-- The honest occurrence bit of the published factory at that code. -/
noncomputable def caseTwoBlockValue
    (factory : ExecutablePointwisePCPPFactory) {n : ℕ}
    (circuit : BooleanCircuit n)
    (nativeInputBits paddedInputBits nativeClauseBits paddedClauseBits
      arity pointCode block : ℕ) : Bool :=
  occurrenceCodeValue factory circuit
    (caseTwoBlockOccurrenceCode nativeInputBits paddedInputBits
      nativeClauseBits paddedClauseBits arity pointCode block)

/-- **One scheduled Case-2 seed value, blockwise.**  Composing the coordinate
lemma of `CaseTwoOccurrenceCoordinates` with the block window above, the seed
value of one XOR copy is the published factory's honest occurrence bit at that
copy's occurrence code. -/
theorem caseTwoBlockValue_eq_seed
    (pcppSource : UniformPointwisePCPPSource)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input)
    {copies target : ℕ} (point : BitInput target)
    (hle :
      copies * seedArity outer pcppSource requiredDegree sourceIndex ≤ target)
    (block : Fin copies) :
    caseTwoBlockValue pcppSource.factory (caseTwoSubstitutedCircuit caseTwo)
        (outer.pcp.nativeWidth (sourceLength sourceIndex))
        (widthEnvelope outer (sourceLength sourceIndex))
        (caseTwoFactoryPCPP pcppSource caseTwo).clauseBits
        (clauseBitsEnvelope outer pcppSource (oracleSizeBound requiredDegree)
          (sourceLength sourceIndex))
        (seedArity outer pcppSource requiredDegree sourceIndex)
        (encodeBitInput point) block.val =
      caseTwoSeed pcppSource caseTwo
        (blockInput
          (fun index :
              Fin (copies *
                seedArity outer pcppSource requiredDegree sourceIndex) =>
            point ⟨index.val, index.isLt.trans_le hle⟩)
          block) := by
  rw [caseTwoSeed_apply_occurrenceCodeValue pcppSource caseTwo
    (blockInput
      (fun index :
          Fin (copies * seedArity outer pcppSource requiredDegree sourceIndex) =>
        point ⟨index.val, index.isLt.trans_le hle⟩)
      block)]
  rw [caseTwoBlockValue, caseTwoBlockOccurrenceCode,
    bitSlice_encodeBitInput_blockInput point hle block]

/-! ## 4. The three framing adapters -/

/-- Build the balanced range request from the requested point code.  The XOR
copy count is the stage's only immediate; the retained context is the point
code itself, so every generated atom is one callable per-block request. -/
def caseTwoBlockRangePrepProgram (copies : ℕ) : NPOracleProgram :=
  [ .set 2 copies 1
  , .pair 2 0 3 2
  , .copy 3 0 3
  , .halt 0
  ]

@[simp] theorem caseTwoBlockRangePrepProgram_oracleFree (copies : ℕ) :
    OracleFree (caseTwoBlockRangePrepProgram copies) := by
  rfl

def caseTwoBlockRangePrepBits (copies pointCode : ℕ) : ℕ :=
  max (natBitLength copies)
    (max (natBitLength pointCode)
      (natBitLength (generatedBalancedRangeInput copies pointCode)))

private theorem run_caseTwoBlockRangePrepProgram
    (inputLength copies pointCode : ℕ) :
    runNPOracleProgram (caseTwoBlockRangePrepProgram copies)
        (caseTwoBlockRangePrepBits copies pointCode) 4
        (initialNPOracleState inputLength pointCode) =
      some (generatedBalancedRangeInput copies pointCode) := by
  have hcopies :
      natBitLength copies ≤ caseTwoBlockRangePrepBits copies pointCode :=
    Nat.le_max_left _ _
  have hpoint :
      natBitLength pointCode ≤ caseTwoBlockRangePrepBits copies pointCode :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have houtput :
      natBitLength (generatedBalancedRangeInput copies pointCode) ≤
        caseTwoBlockRangePrepBits copies pointCode :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  rw [show 4 = 3 + 1 by omega]
  rw [run_set_instruction (value := copies) (by rfl) rfl hcopies]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := generatedBalancedRangeInput copies pointCode) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
      generatedBalancedRangeInput])
    houtput]
  rw [show 2 = 1 + 1 by omega]
  rw [run_copy_instruction
    (value := generatedBalancedRangeInput copies pointCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Drop the context the range generator retains beside the request tree. -/
def caseTwoBlockTakeLeftProgram : NPOracleProgram :=
  [ .unpairLeft 0 0 1
  , .halt 0
  ]

@[simp] theorem caseTwoBlockTakeLeftProgram_oracleFree :
    OracleFree caseTwoBlockTakeLeftProgram := by
  rfl

theorem run_caseTwoBlockTakeLeftProgram
    {maximumBits : ℕ} (inputLength left right : ℕ)
    (hleft : natBitLength left ≤ maximumBits) :
    runNPOracleProgram caseTwoBlockTakeLeftProgram maximumBits 2
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some left := by
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := left) (by rfl) rfl
    (by simp [initialNPOracleState]) hleft]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hleft

/-- Attach the Case-2 dispatch tag expected by the fixed target-bit
dispatcher. -/
def caseTwoBlockTagProgram : NPOracleProgram :=
  [ .set 2 1 1
  , .pair 2 0 3 2
  , .copy 3 0 3
  , .halt 0
  ]

@[simp] theorem caseTwoBlockTagProgram_oracleFree :
    OracleFree caseTwoBlockTagProgram := by
  rfl

def caseTwoBlockTagBits (bits : List Bool) : ℕ :=
  max 1
    (max (natBitLength (encodeBalancedList (bits.map Bool.toNat)))
      (natBitLength (targetBitCaseTwoInput bits)))

theorem run_caseTwoBlockTagProgram
    (inputLength : ℕ) (bits : List Bool) :
    runNPOracleProgram caseTwoBlockTagProgram (caseTwoBlockTagBits bits) 4
        (initialNPOracleState inputLength
          (encodeBalancedList (bits.map Bool.toNat))) =
      some (targetBitCaseTwoInput bits) := by
  have hone : natBitLength 1 ≤ caseTwoBlockTagBits bits := by
    have hbit : natBitLength 1 = 1 := by simp [natBitLength]
    rw [hbit]
    exact Nat.le_max_left _ _
  have hlist :
      natBitLength (encodeBalancedList (bits.map Bool.toNat)) ≤
        caseTwoBlockTagBits bits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have houtput :
      natBitLength (targetBitCaseTwoInput bits) ≤ caseTwoBlockTagBits bits :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  rw [show 4 = 3 + 1 by omega]
  rw [run_set_instruction (value := 1) (by rfl) rfl hone]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := targetBitCaseTwoInput bits) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
      targetBitCaseTwoInput])
    houtput]
  rw [show 2 = 1 + 1 by omega]
  rw [run_copy_instruction (value := targetBitCaseTwoInput bits) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 5. The block-list stage -/

private theorem le_foldr_max_of_mem {value : ℕ} {values : List ℕ}
    (hmem : value ∈ values) : value ≤ values.foldr max 0 := by
  induction values with
  | nil => exact absurd hmem (List.not_mem_nil)
  | cons head rest inductionHypothesis =>
      rcases List.mem_cons.mp hmem with hhead | htail
      · exact hhead ▸ Nat.le_max_left _ _
      · exact (inductionHypothesis htail).trans (Nat.le_max_right _ _)

/-- The generator's own atom list at one requested point code. -/
def caseTwoBlockAtoms (inputLength copies pointCode : ℕ) : List ℕ :=
  (List.range copies).map fun block =>
    balancedRangeRequestAtom inputLength block pointCode

private theorem balancedRangeRequestAtoms_eq_caseTwoBlockAtoms
    (inputLength copies pointCode : ℕ) :
    balancedRangeRequestAtoms inputLength pointCode 0 copies =
      caseTwoBlockAtoms inputLength copies pointCode := by
  rw [balancedRangeRequestAtoms_eq_map_range]
  simp [caseTwoBlockAtoms]

/-- XOR copy index recovered from one generated atom. -/
def caseTwoBlockAtomIndex (atom : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair atom).2).1

@[simp] theorem caseTwoBlockAtomIndex_atom
    (inputLength block context : ℕ) :
    caseTwoBlockAtomIndex
        (balancedRangeRequestAtom inputLength block context) = block := by
  simp [caseTwoBlockAtomIndex, balancedRangeRequestAtom]

private theorem caseTwoBlockAtoms_outputs
    (inputLength copies pointCode : ℕ) (value : ℕ → Bool) :
    (caseTwoBlockAtoms inputLength copies pointCode).map
        (fun atom => (value (caseTwoBlockAtomIndex atom)).toNat) =
      ((List.range copies).map value).map Bool.toNat := by
  rw [caseTwoBlockAtoms, List.map_map, List.map_map]
  exact List.map_congr_left fun block _ => by simp

/-- **The Case-2 seed block list.**  One fixed program, parameterized by the
XOR copy count and by the per-block occurrence callee, turning the requested
point code into the dispatcher's Case-2 input. -/
def caseTwoSeedBlockListProgram (occurrence : NPOracleProgram)
    (copies : ℕ) : NPOracleProgram :=
  linkPrograms (caseTwoBlockRangePrepProgram copies) <|
    linkPrograms generatedBalancedRangeProgram <|
      linkPrograms caseTwoBlockTakeLeftProgram <|
        linkPrograms (balancedCallProgram occurrence) caseTwoBlockTagProgram

theorem caseTwoSeedBlockListProgram_oracleFree
    {occurrence : NPOracleProgram} (hoccurrence : OracleFree occurrence)
    (copies : ℕ) :
    OracleFree (caseTwoSeedBlockListProgram occurrence copies) := by
  apply oracleFree_linkPrograms (caseTwoBlockRangePrepProgram_oracleFree copies)
  apply oracleFree_linkPrograms generatedBalancedRangeProgram_oracleFree
  apply oracleFree_linkPrograms caseTwoBlockTakeLeftProgram_oracleFree
  exact oracleFree_linkPrograms (balancedCallProgram_oracleFree hoccurrence)
    caseTwoBlockTagProgram_oracleFree

/-- The callee's certified output on one generated atom. -/
noncomputable def caseTwoBlockAtomOutput (value : ℕ → Bool) (atom : ℕ) : ℕ :=
  (value (caseTwoBlockAtomIndex atom)).toNat

def caseTwoSeedBlockListFuel (occurrence : NPOracleProgram)
    (inputLength copies pointCode : ℕ) (occurrenceFuel : ℕ → ℕ) : ℕ :=
  linkFuel
    (linkPrograms generatedBalancedRangeProgram
      (linkPrograms caseTwoBlockTakeLeftProgram
        (linkPrograms (balancedCallProgram occurrence)
          caseTwoBlockTagProgram)))
    4 <|
    linkFuel
      (linkPrograms caseTwoBlockTakeLeftProgram
        (linkPrograms (balancedCallProgram occurrence)
          caseTwoBlockTagProgram))
      (generatedBalancedRangeFuel inputLength copies pointCode) <|
      linkFuel
        (linkPrograms (balancedCallProgram occurrence) caseTwoBlockTagProgram)
        2 <|
        linkFuel caseTwoBlockTagProgram
          (balancedCallFuel occurrence
            (fun atom => occurrenceFuel (caseTwoBlockAtomIndex atom))
            (caseTwoBlockAtoms inputLength copies pointCode))
          4

noncomputable def caseTwoSeedBlockListBits
    (inputLength copies pointCode : ℕ) (occurrenceBits : ℕ → ℕ)
    (value : ℕ → Bool) (bits : List Bool) : ℕ :=
  max 1 <|
    max (natBitLength inputLength) <|
      max (caseTwoBlockRangePrepBits copies pointCode) <|
        max
          (generatedBalancedRangeRequiredBits inputLength copies pointCode) <|
          max
            (natBitLength
              (encodeBalancedList
                (caseTwoBlockAtoms inputLength copies pointCode))) <|
            max
              (balancedCallRequiredBits (caseTwoBlockAtomOutput value)
                (caseTwoBlockAtoms inputLength copies pointCode)) <|
              max
                (((caseTwoBlockAtoms inputLength copies pointCode).map
                  fun atom =>
                    occurrenceBits (caseTwoBlockAtomIndex atom)).foldr max 0)
                (caseTwoBlockTagBits bits)

/-- **Exact execution of the block-list stage.**  Modulo the single per-block
occurrence callee, one fixed oracle-free program turns the requested point code
into the exact Case-2 input of the fixed target-bit dispatcher. -/
theorem run_caseTwoSeedBlockListProgram
    (occurrence : NPOracleProgram)
    (inputLength copies pointCode : ℕ)
    (occurrenceBits occurrenceFuel : ℕ → ℕ) (value : ℕ → Bool)
    (hoccurrence : ∀ block, block < copies →
      runNPOracleProgram occurrence (occurrenceBits block)
          (occurrenceFuel block)
          (initialNPOracleState inputLength (Nat.pair block pointCode)) =
        some (value block).toNat) :
    runNPOracleProgram (caseTwoSeedBlockListProgram occurrence copies)
        (caseTwoSeedBlockListBits inputLength copies pointCode occurrenceBits
          value ((List.range copies).map value))
        (caseTwoSeedBlockListFuel occurrence inputLength copies pointCode
          occurrenceFuel)
        (initialNPOracleState inputLength pointCode) =
      some (targetBitCaseTwoInput ((List.range copies).map value)) := by
  set bits := (List.range copies).map value with hbits
  set atoms := caseTwoBlockAtoms inputLength copies pointCode with hatoms
  set maximumBits :=
    caseTwoSeedBlockListBits inputLength copies pointCode occurrenceBits value
      bits with hmaximumBits
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hlengthBits : natBitLength inputLength ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hprepBits :
      caseTwoBlockRangePrepBits copies pointCode ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hrangeBits :
      generatedBalancedRangeRequiredBits inputLength copies pointCode ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlistBits :
      natBitLength (encodeBalancedList atoms) ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcallBits :
      balancedCallRequiredBits (caseTwoBlockAtomOutput value) atoms ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hatomBits :
      (atoms.map fun atom =>
          occurrenceBits (caseTwoBlockAtomIndex atom)).foldr max 0 ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans <|
              (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have htagBits : caseTwoBlockTagBits bits ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans <|
            (Nat.le_max_right _ _).trans <|
              (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hprep :
      runNPOracleProgram (caseTwoBlockRangePrepProgram copies) maximumBits 4
          (initialNPOracleState inputLength pointCode) =
        some (generatedBalancedRangeInput copies pointCode) :=
    run_bits_mono
      (run_caseTwoBlockRangePrepProgram inputLength copies pointCode)
      hprepBits
  have hrange :
      runNPOracleProgram generatedBalancedRangeProgram maximumBits
          (generatedBalancedRangeFuel inputLength copies pointCode)
          (initialNPOracleState inputLength
            (generatedBalancedRangeInput copies pointCode)) =
        some (Nat.pair (encodeBalancedList atoms) pointCode) := by
    rw [hatoms, ← balancedRangeRequestAtoms_eq_caseTwoBlockAtoms]
    exact run_bits_mono
      (run_generatedBalancedRangeProgram inputLength copies pointCode)
      hrangeBits
  have htake :
      runNPOracleProgram caseTwoBlockTakeLeftProgram maximumBits 2
          (initialNPOracleState inputLength
            (Nat.pair (encodeBalancedList atoms) pointCode)) =
        some (encodeBalancedList atoms) :=
    run_caseTwoBlockTakeLeftProgram inputLength (encodeBalancedList atoms)
      pointCode hlistBits
  have hcall :
      runNPOracleProgram (balancedCallProgram occurrence) maximumBits
          (balancedCallFuel occurrence
            (fun atom => occurrenceFuel (caseTwoBlockAtomIndex atom)) atoms)
          (initialNPOracleState inputLength (encodeBalancedList atoms)) =
        some (encodeBalancedList (bits.map Bool.toNat)) := by
    rw [hbits, ← caseTwoBlockAtoms_outputs inputLength copies pointCode value]
    refine run_balancedCallProgram_from inputLength atoms
      (fun atom => occurrenceFuel (caseTwoBlockAtomIndex atom))
      (caseTwoBlockAtomOutput value) hcallBits ?_
    intro atom hatom
    have hcalleeBits :
        occurrenceBits (caseTwoBlockAtomIndex atom) ≤ maximumBits :=
      (le_foldr_max_of_mem (List.mem_map_of_mem hatom)).trans hatomBits
    rw [hatoms, caseTwoBlockAtoms, List.mem_map] at hatom
    obtain ⟨block, hblock, hatomEq⟩ := hatom
    rw [← hatomEq] at hcalleeBits ⊢
    rw [caseTwoBlockAtomIndex_atom] at hcalleeBits
    have hleft :
        (Nat.unpair
          (balancedRangeRequestAtom inputLength block pointCode)).1 =
          inputLength := by
      simp [balancedRangeRequestAtom]
    have hright :
        (Nat.unpair
          (balancedRangeRequestAtom inputLength block pointCode)).2 =
          Nat.pair block pointCode := by
      simp [balancedRangeRequestAtom]
    rw [hleft, hright, caseTwoBlockAtomOutput, caseTwoBlockAtomIndex_atom]
    exact run_bits_mono
      (hoccurrence block (List.mem_range.mp hblock)) hcalleeBits
  have htag :
      runNPOracleProgram caseTwoBlockTagProgram maximumBits 4
          (initialNPOracleState inputLength
            (encodeBalancedList (bits.map Bool.toNat))) =
        some (targetBitCaseTwoInput bits) :=
    run_bits_mono (run_caseTwoBlockTagProgram inputLength bits) htagBits
  have hfourth := run_linkPrograms hpositive hlengthBits hcall htag
  have hthird := run_linkPrograms hpositive hlengthBits htake hfourth
  have hsecond := run_linkPrograms hpositive hlengthBits hrange hthird
  exact run_linkPrograms hpositive hlengthBits hprep hsecond

/-! ## 6. The Case-2 target bit from the requested point code -/

/-- The scheduled per-block value: the honest occurrence bit of the published
factory at the occurrence code of one XOR copy of the requested point. -/
noncomputable def caseTwoScheduledBlockValue
    (pcppSource : UniformPointwisePCPPSource)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input)
    (pointCode block : ℕ) : Bool :=
  caseTwoBlockValue pcppSource.factory (caseTwoSubstitutedCircuit caseTwo)
    (outer.pcp.nativeWidth (sourceLength sourceIndex))
    (widthEnvelope outer (sourceLength sourceIndex))
    (caseTwoFactoryPCPP pcppSource caseTwo).clauseBits
    (clauseBitsEnvelope outer pcppSource (oracleSizeBound requiredDegree)
      (sourceLength sourceIndex))
    (seedArity outer pcppSource requiredDegree sourceIndex) pointCode block

theorem caseTwoScheduledBlockValue_eq_seed
    (pcppSource : UniformPointwisePCPPSource)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input)
    {copies target : ℕ} (point : BitInput target)
    (hle :
      copies * seedArity outer pcppSource requiredDegree sourceIndex ≤ target)
    (block : Fin copies) :
    caseTwoScheduledBlockValue pcppSource caseTwo (encodeBitInput point)
        block.val =
      caseTwoSeed pcppSource caseTwo
        (blockInput
          (fun index :
              Fin (copies *
                seedArity outer pcppSource requiredDegree sourceIndex) =>
            point ⟨index.val, index.isLt.trans_le hle⟩)
          block) :=
  caseTwoBlockValue_eq_seed pcppSource caseTwo point hle block

/-- One fixed program computing a Case-2 target bit from the requested point
code: the block-list stage of §5, then the published target-bit dispatcher. -/
def caseTwoTargetBitFromPointRangeProgram
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (occurrence : NPOracleProgram) (copies : ℕ) : NPOracleProgram :=
  linkPrograms (caseTwoSeedBlockListProgram occurrence copies)
    (targetBitProgram algorithm)

theorem caseTwoTargetBitFromPointRangeProgram_oracleFree
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    {occurrence : NPOracleProgram} (hoccurrence : OracleFree occurrence)
    (copies : ℕ) :
    OracleFree
      (caseTwoTargetBitFromPointRangeProgram algorithm occurrence copies) :=
  oracleFree_linkPrograms
    (caseTwoSeedBlockListProgram_oracleFree hoccurrence copies)
    (targetBitProgram_oracleFree algorithm)

def caseTwoTargetBitFromPointRangeFuel
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (occurrence : NPOracleProgram) (inputLength copies pointCode : ℕ)
    (occurrenceFuel : ℕ → ℕ) (bits : List Bool) : ℕ :=
  linkFuel (targetBitProgram algorithm)
    (caseTwoSeedBlockListFuel occurrence inputLength copies pointCode
      occurrenceFuel)
    (targetBitCaseTwoFuel bits)

noncomputable def caseTwoTargetBitFromPointRangeBits
    (inputLength copies pointCode : ℕ) (occurrenceBits : ℕ → ℕ)
    (value : ℕ → Bool) (bits : List Bool) : ℕ :=
  occurrenceStageBits inputLength
    (caseTwoSeedBlockListBits inputLength copies pointCode occurrenceBits value
      bits)
    (targetBitCaseTwoBits inputLength bits)

/-- **Exact Case-2 execution from the requested point code.**  Modulo the
single per-block occurrence callee, one fixed oracle-free program returns the
XOR-amplified seed bit the Case-2 branch of the canonical target is defined
by. -/
theorem run_caseTwoTargetBitFromPointRangeProgram
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (occurrence : NPOracleProgram)
    (pcppSource : UniformPointwisePCPPSource)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input)
    {copies target : ℕ} (point : BitInput target)
    (hle :
      copies * seedArity outer pcppSource requiredDegree sourceIndex ≤ target)
    (occurrenceBits occurrenceFuel : ℕ → ℕ)
    (hoccurrence : ∀ block, block < copies →
      runNPOracleProgram occurrence (occurrenceBits block)
          (occurrenceFuel block)
          (initialNPOracleState target
            (Nat.pair block (encodeBitInput point))) =
        some
          (caseTwoScheduledBlockValue pcppSource caseTwo
            (encodeBitInput point) block).toNat) :
    runNPOracleProgram
        (caseTwoTargetBitFromPointRangeProgram algorithm occurrence copies)
        (caseTwoTargetBitFromPointRangeBits target copies
          (encodeBitInput point) occurrenceBits
          (caseTwoScheduledBlockValue pcppSource caseTwo
            (encodeBitInput point))
          ((List.range copies).map
            (caseTwoScheduledBlockValue pcppSource caseTwo
              (encodeBitInput point))))
        (caseTwoTargetBitFromPointRangeFuel algorithm occurrence target copies
          (encodeBitInput point) occurrenceFuel
          ((List.range copies).map
            (caseTwoScheduledBlockValue pcppSource caseTwo
              (encodeBitInput point))))
        (initialNPOracleState target (encodeBitInput point)) =
      some
        (xorPower (caseTwoSeed pcppSource caseTwo) copies
          (fun index :
              Fin (copies *
                seedArity outer pcppSource requiredDegree sourceIndex) =>
            point ⟨index.val, index.isLt.trans_le hle⟩)).toNat := by
  have hparity :
      (((List.range copies).map
            (caseTwoScheduledBlockValue pcppSource caseTwo
              (encodeBitInput point))).foldl xor false) =
        xorPower (caseTwoSeed pcppSource caseTwo) copies
          (fun index :
              Fin (copies *
                seedArity outer pcppSource requiredDegree sourceIndex) =>
            point ⟨index.val, index.isLt.trans_le hle⟩) :=
    xorPower_eq_foldl_range (caseTwoSeed pcppSource caseTwo)
      (fun index :
          Fin (copies * seedArity outer pcppSource requiredDegree sourceIndex) =>
        point ⟨index.val, index.isLt.trans_le hle⟩)
      (caseTwoScheduledBlockValue pcppSource caseTwo (encodeBitInput point))
      (fun block =>
        caseTwoScheduledBlockValue_eq_seed pcppSource caseTwo point hle block)
  rw [← hparity]
  exact run_occurrenceStage
    (run_caseTwoSeedBlockListProgram occurrence target copies
      (encodeBitInput point) occurrenceBits occurrenceFuel
      (caseTwoScheduledBlockValue pcppSource caseTwo (encodeBitInput point))
      hoccurrence)
    (run_targetBitProgram_caseTwo algorithm target
      ((List.range copies).map
        (caseTwoScheduledBlockValue pcppSource caseTwo
          (encodeBitInput point))))

/-! ## 7. Both published schedules -/

/-- **The inverse schedule's Case-2 target bit.**  Modulo the single per-block
occurrence callee, the composed program returns exactly the canonical
Case-1/Case-2 target of the inverse schedule at every requested input. -/
theorem run_caseTwoTargetBitFromPointRangeProgram_inverse
    (occurrence : NPOracleProgram)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ)
    (hlarge :
      inverseCaseOneTargetOnset contracts outer advantageExponent ≤ target)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (hrejects : ¬machine.toSemantic.accepts
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (haccepts : ∀ caseTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent)))
        (paddedOuterPCP outer)
        (inverseRefuterInput contracts outer machine advantageExponent target),
      InverseCaseTwoAcceptance contracts outer
        (inverseCoreAdvantagePower advantageExponent)
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)
        caseTwo machine)
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (paddedOuterPCP outer)
      (inverseRefuterInput contracts outer machine advantageExponent target))
    (hbranch :
      inverseTargetBranch contracts outer machine advantageExponent target
          hyes = .caseTwo caseTwo)
    (point : BitInput target) (occurrenceBits occurrenceFuel : ℕ → ℕ)
    (hoccurrence : ∀ block,
      block <
        inverseCopies outer (publishedPointwisePCPP contracts)
          (inverseRate contracts (inverseCoreAdvantagePower advantageExponent))
          (inverseSourceIndex
            (inverseSelectedSource contracts outer
              (inverseCoreAdvantagePower advantageExponent) target)) →
      runNPOracleProgram occurrence (occurrenceBits block)
          (occurrenceFuel block)
          (initialNPOracleState target
            (Nat.pair block (encodeBitInput point))) =
        some
          (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
            caseTwo (encodeBitInput point) block).toNat) :
    runNPOracleProgram
        (caseTwoTargetBitFromPointRangeProgram
          (publishedAmplifier contracts).algorithm occurrence
          (inverseCopies outer (publishedPointwisePCPP contracts)
            (inverseRate contracts
              (inverseCoreAdvantagePower advantageExponent))
            (inverseSourceIndex
              (inverseSelectedSource contracts outer
                (inverseCoreAdvantagePower advantageExponent) target))))
        (caseTwoTargetBitFromPointRangeBits target
          (inverseCopies outer (publishedPointwisePCPP contracts)
            (inverseRate contracts
              (inverseCoreAdvantagePower advantageExponent))
            (inverseSourceIndex
              (inverseSelectedSource contracts outer
                (inverseCoreAdvantagePower advantageExponent) target)))
          (encodeBitInput point) occurrenceBits
          (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
            caseTwo (encodeBitInput point))
          ((List.range
            (inverseCopies outer (publishedPointwisePCPP contracts)
              (inverseRate contracts
                (inverseCoreAdvantagePower advantageExponent))
              (inverseSourceIndex
                (inverseSelectedSource contracts outer
                  (inverseCoreAdvantagePower advantageExponent) target)))).map
            (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
              caseTwo (encodeBitInput point))))
        (caseTwoTargetBitFromPointRangeFuel
          (publishedAmplifier contracts).algorithm occurrence target
          (inverseCopies outer (publishedPointwisePCPP contracts)
            (inverseRate contracts
              (inverseCoreAdvantagePower advantageExponent))
            (inverseSourceIndex
              (inverseSelectedSource contracts outer
                (inverseCoreAdvantagePower advantageExponent) target)))
          (encodeBitInput point) occurrenceFuel
          ((List.range
            (inverseCopies outer (publishedPointwisePCPP contracts)
              (inverseRate contracts
                (inverseCoreAdvantagePower advantageExponent))
              (inverseSourceIndex
                (inverseSelectedSource contracts outer
                  (inverseCoreAdvantagePower advantageExponent) target)))).map
            (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
              caseTwo (encodeBitInput point))))
        (initialNPOracleState target (encodeBitInput point)) =
      some
        (inverseCanonicalTargetFunction contracts outer machine
          advantageExponent target hlarge hyes hrejects haccepts
          point).toNat := by
  rw [inverseCanonicalTargetFunction_caseTwo_apply contracts outer machine
    advantageExponent target hlarge hyes hrejects haccepts caseTwo hbranch
    point]
  exact run_caseTwoTargetBitFromPointRangeProgram
    (publishedAmplifier contracts).algorithm occurrence
    (publishedPointwisePCPP contracts) caseTwo point
    (inverseCaseTwoRawArity_le_target contracts outer
      (inverseCoreAdvantagePower advantageExponent) target
      (inverseCaseOneTargetOnset_ready contracts outer advantageExponent target
        hlarge).1)
    occurrenceBits occurrenceFuel hoccurrence

/-- Fixed-rate counterpart of
`run_caseTwoTargetBitFromPointRangeProgram_inverse`. -/
theorem run_caseTwoTargetBitFromPointRangeProgram_fixed
    (occurrence : NPOracleProgram)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ)
    (hlarge : fixedCaseOneTargetOnset contracts outer requestedRate ≤ target)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength
        (fixedSelectedSource contracts outer requestedRate target))
      (fixedRefuterInput contracts outer machine requestedRate target))
    (hrejects : ¬machine.toSemantic.accepts
      (fixedRefuterInput contracts outer machine requestedRate target))
    (haccepts : ∀ caseTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (fixedRequiredDegree contracts requestedRate))
        (paddedOuterPCP outer)
        (fixedRefuterInput contracts outer machine requestedRate target),
      FixedCaseTwoAcceptance contracts outer requestedRate
        (fixedSelectedSource contracts outer requestedRate target)
        caseTwo machine)
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP outer)
      (fixedRefuterInput contracts outer machine requestedRate target))
    (hbranch :
      fixedTargetBranch contracts outer machine requestedRate target hyes =
        .caseTwo caseTwo)
    (point : BitInput target) (occurrenceBits occurrenceFuel : ℕ → ℕ)
    (hoccurrence : ∀ block,
      block < fixedCopies (publishedPointwisePCPP contracts)
          (fixedRate contracts requestedRate) →
      runNPOracleProgram occurrence (occurrenceBits block)
          (occurrenceFuel block)
          (initialNPOracleState target
            (Nat.pair block (encodeBitInput point))) =
        some
          (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
            caseTwo (encodeBitInput point) block).toNat) :
    runNPOracleProgram
        (caseTwoTargetBitFromPointRangeProgram
          (publishedAmplifier contracts).algorithm occurrence
          (fixedCopies (publishedPointwisePCPP contracts) (fixedRate contracts requestedRate)))
        (caseTwoTargetBitFromPointRangeBits target
          (fixedCopies (publishedPointwisePCPP contracts) (fixedRate contracts requestedRate))
          (encodeBitInput point) occurrenceBits
          (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
            caseTwo (encodeBitInput point))
          ((List.range
            (fixedCopies (publishedPointwisePCPP contracts)
              (fixedRate contracts requestedRate))).map
            (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
              caseTwo (encodeBitInput point))))
        (caseTwoTargetBitFromPointRangeFuel
          (publishedAmplifier contracts).algorithm occurrence target
          (fixedCopies (publishedPointwisePCPP contracts) (fixedRate contracts requestedRate))
          (encodeBitInput point) occurrenceFuel
          ((List.range
            (fixedCopies (publishedPointwisePCPP contracts)
              (fixedRate contracts requestedRate))).map
            (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
              caseTwo (encodeBitInput point))))
        (initialNPOracleState target (encodeBitInput point)) =
      some
        (fixedCanonicalTargetFunction contracts outer machine requestedRate
          target hlarge hyes hrejects haccepts point).toNat := by
  rw [fixedCanonicalTargetFunction_caseTwo_apply contracts outer machine
    requestedRate target hlarge hyes hrejects haccepts caseTwo hbranch point]
  exact run_caseTwoTargetBitFromPointRangeProgram
    (publishedAmplifier contracts).algorithm occurrence
    (publishedPointwisePCPP contracts) caseTwo point
    (fixedCaseTwoRawArity_le_target contracts outer requestedRate target
      (fixedCaseOneTargetOnset_ready contracts outer requestedRate target
        hlarge).1)
    occurrenceBits occurrenceFuel hoccurrence

end NearCubicWires.CaseTwoSeedBlockListProgram
