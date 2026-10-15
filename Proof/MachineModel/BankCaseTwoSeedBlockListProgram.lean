import Proof.MachineModel.BankScheduleDiagonal
import Proof.MachineModel.CaseTwoSeedBlockListProgram

/-!
# The Case-2 seed block list, driven from the numeral bank's registers

`CaseTwoSeedBlockListProgram.caseTwoSeedBlockListProgram` carries exactly one
target-derived immediate: the XOR copy count, frozen by the `set` instruction
of `caseTwoBlockRangePrepProgram`.  On the fixed schedule that immediate is
harmless — `RecoveryScheduleEnvelope.fixedCopies` does not depend on the
scheduled width, so `EmittedBranchTargetProgram.fixedCaseTwoChainProgram_target_independent`
already records that the whole chain is request-independent.  On the *inverse*
schedule the copy count is `inverseCopies outer pcppSource rate sourceIndex`,
which grows with the scheduled width, and the immediate is therefore the last
target-derived numeral of the Case-2 branch.

`RuntimeScheduleNumeralBank` leaves that very numeral in a register: the bank's
frame is

`pair sourceLength (pair width (pair queryCount (pair copies pointCode)))`.

This module replaces the prep stage's `set` by three `unpairRight`
instructions, so the range generator's input `pair copies pointCode` is read
rather than baked, and re-derives the composed run of the block-list stage, of
the Case-2 target bit, and of the inverse schedule's Case-2 chain — all from
the bank's frame, with no schedule immediate anywhere in the stream.

The single remaining parameter is unchanged: the per-block occurrence callee of
`CaseTwoSeedBlockListProgram`.
-/

namespace NearCubicWires.BankCaseTwoSeedBlockListProgram

open NearCubicWires
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoSeedBlockListProgram
open NearCubicWires.CaseTwoTargetLanguageClosure
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The range request, read from the bank's copy register -/

/-- Read the bank's frame down to its copy register: the pair
`pair copies pointCode` the balanced range generator consumes is the third
right projection of the frame, so no numeral is frozen in the stream. -/
def bankCaseTwoBlockRangePrepProgram : NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .unpairRight 2 3 2
  , .unpairRight 3 0 3
  , .halt 0
  ]

@[simp] theorem bankCaseTwoBlockRangePrepProgram_oracleFree :
    OracleFree bankCaseTwoBlockRangePrepProgram := by
  rfl

def bankCaseTwoBlockRangePrepBits
    (sourceLen width queryCount copies pointCode : ℕ) : ℕ :=
  natBitLength
    (scheduleNumeralBankOutput sourceLen width queryCount copies pointCode)

/-- **The register-driven range request, executed.**  The bank's frame in, the
generator's input `pair copies pointCode` out. -/
theorem run_bankCaseTwoBlockRangePrepProgram
    (inputLength sourceLen width queryCount copies pointCode : ℕ) :
    runNPOracleProgram bankCaseTwoBlockRangePrepProgram
        (bankCaseTwoBlockRangePrepBits sourceLen width queryCount copies
          pointCode)
        4
        (initialNPOracleState inputLength
          (scheduleNumeralBankOutput sourceLen width queryCount copies
            pointCode)) =
      some (generatedBalancedRangeInput copies pointCode) := by
  have hbits : ∀ value : ℕ,
      value ≤
        scheduleNumeralBankOutput sourceLen width queryCount copies pointCode →
      natBitLength value ≤
        bankCaseTwoBlockRangePrepBits sourceLen width queryCount copies
          pointCode :=
    fun _ hvalue => natBitLength_mono hvalue
  have hfirst :
      natBitLength
          (Nat.pair width (Nat.pair queryCount (Nat.pair copies pointCode))) ≤
        bankCaseTwoBlockRangePrepBits sourceLen width queryCount copies
          pointCode :=
    hbits _ (Nat.right_le_pair _ _)
  have hsecond :
      natBitLength (Nat.pair queryCount (Nat.pair copies pointCode)) ≤
        bankCaseTwoBlockRangePrepBits sourceLen width queryCount copies
          pointCode :=
    hbits _ ((Nat.right_le_pair _ _).trans (Nat.right_le_pair _ _))
  have houtput :
      natBitLength (generatedBalancedRangeInput copies pointCode) ≤
        bankCaseTwoBlockRangePrepBits sourceLen width queryCount copies
          pointCode :=
    hbits _
      ((Nat.right_le_pair _ _).trans
        ((Nat.right_le_pair _ _).trans (Nat.right_le_pair _ _)))
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair width (Nat.pair queryCount (Nat.pair copies pointCode)))
    (by rfl) rfl
    (by simp [initialNPOracleState, scheduleNumeralBankOutput]) hfirst]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair queryCount (Nat.pair copies pointCode)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsecond]
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := generatedBalancedRangeInput copies pointCode) (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        generatedBalancedRangeInput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 2. The block-list stage from the bank's frame -/

private theorem le_foldr_max_of_mem {value : ℕ} {values : List ℕ}
    (hmem : value ∈ values) : value ≤ values.foldr max 0 := by
  induction values with
  | nil => exact absurd hmem (List.not_mem_nil)
  | cons head rest inductionHypothesis =>
      rcases List.mem_cons.mp hmem with hhead | htail
      · exact hhead ▸ Nat.le_max_left _ _
      · exact (inductionHypothesis htail).trans (Nat.le_max_right _ _)

private theorem balancedRangeRequestAtoms_eq_caseTwoBlockAtoms
    (inputLength copies pointCode : ℕ) :
    balancedRangeRequestAtoms inputLength pointCode 0 copies =
      caseTwoBlockAtoms inputLength copies pointCode := by
  rw [balancedRangeRequestAtoms_eq_map_range]
  simp [caseTwoBlockAtoms]

private theorem caseTwoBlockAtoms_outputs
    (inputLength copies pointCode : ℕ) (value : ℕ → Bool) :
    (caseTwoBlockAtoms inputLength copies pointCode).map
        (fun atom => (value (caseTwoBlockAtomIndex atom)).toNat) =
      ((List.range copies).map value).map Bool.toNat := by
  rw [caseTwoBlockAtoms, List.map_map, List.map_map]
  exact List.map_congr_left fun block _ => by simp

/-- **The register-driven Case-2 seed block list.**  One fixed program,
parameterized only by the per-block occurrence callee: the XOR copy count is a
register read of the numeral bank's frame. -/
def bankCaseTwoSeedBlockListProgram (occurrence : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms bankCaseTwoBlockRangePrepProgram <|
    linkPrograms generatedBalancedRangeProgram <|
      linkPrograms caseTwoBlockTakeLeftProgram <|
        linkPrograms (balancedCallProgram occurrence) caseTwoBlockTagProgram

theorem bankCaseTwoSeedBlockListProgram_oracleFree
    {occurrence : NPOracleProgram} (hoccurrence : OracleFree occurrence) :
    OracleFree (bankCaseTwoSeedBlockListProgram occurrence) := by
  apply oracleFree_linkPrograms bankCaseTwoBlockRangePrepProgram_oracleFree
  apply oracleFree_linkPrograms generatedBalancedRangeProgram_oracleFree
  apply oracleFree_linkPrograms caseTwoBlockTakeLeftProgram_oracleFree
  exact oracleFree_linkPrograms (balancedCallProgram_oracleFree hoccurrence)
    caseTwoBlockTagProgram_oracleFree

def bankCaseTwoSeedBlockListFuel (occurrence : NPOracleProgram)
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

noncomputable def bankCaseTwoSeedBlockListBits
    (inputLength sourceLen width queryCount copies pointCode : ℕ)
    (occurrenceBits : ℕ → ℕ) (value : ℕ → Bool) (bits : List Bool) : ℕ :=
  max 1 <|
    max (natBitLength inputLength) <|
      max
        (bankCaseTwoBlockRangePrepBits sourceLen width queryCount copies
          pointCode) <|
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

set_option maxHeartbeats 800000 in
-- The five nested link terms force Lean to elaborate the whole stage's fuel.
/-- **Exact execution of the register-driven block-list stage.**  Modulo the
single per-block occurrence callee, one fixed oracle-free program turns the
numeral bank's frame into the dispatcher's Case-2 input; the XOR copy count is
the bank's own register. -/
theorem run_bankCaseTwoSeedBlockListProgram
    (occurrence : NPOracleProgram)
    (inputLength sourceLen width queryCount copies pointCode : ℕ)
    (occurrenceBits occurrenceFuel : ℕ → ℕ) (value : ℕ → Bool)
    (hoccurrence : ∀ block, block < copies →
      runNPOracleProgram occurrence (occurrenceBits block)
          (occurrenceFuel block)
          (initialNPOracleState inputLength (Nat.pair block pointCode)) =
        some (value block).toNat) :
    runNPOracleProgram (bankCaseTwoSeedBlockListProgram occurrence)
        (bankCaseTwoSeedBlockListBits inputLength sourceLen width queryCount
          copies pointCode occurrenceBits value
          ((List.range copies).map value))
        (bankCaseTwoSeedBlockListFuel occurrence inputLength copies pointCode
          occurrenceFuel)
        (initialNPOracleState inputLength
          (scheduleNumeralBankOutput sourceLen width queryCount copies
            pointCode)) =
      some (targetBitCaseTwoInput ((List.range copies).map value)) := by
  set bits := (List.range copies).map value with hbits
  set atoms := caseTwoBlockAtoms inputLength copies pointCode with hatoms
  set maximumBits :=
    bankCaseTwoSeedBlockListBits inputLength sourceLen width queryCount copies
      pointCode occurrenceBits value bits with hmaximumBits
  have hpositive : 1 ≤ maximumBits := Nat.le_max_left _ _
  have hlengthBits : natBitLength inputLength ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hprepBits :
      bankCaseTwoBlockRangePrepBits sourceLen width queryCount copies
          pointCode ≤
        maximumBits :=
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
      runNPOracleProgram bankCaseTwoBlockRangePrepProgram maximumBits 4
          (initialNPOracleState inputLength
            (scheduleNumeralBankOutput sourceLen width queryCount copies
              pointCode)) =
        some (generatedBalancedRangeInput copies pointCode) :=
    run_bits_mono
      (run_bankCaseTwoBlockRangePrepProgram inputLength sourceLen width
        queryCount copies pointCode)
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

/-! ## 3. The Case-2 target bit from the bank's frame -/

/-- One fixed program computing a Case-2 target bit from the numeral bank's
frame: the register-driven block-list stage of §2, then the published
target-bit dispatcher.  No schedule numeral is frozen in the stream. -/
def bankCaseTwoTargetBitProgram
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (occurrence : NPOracleProgram) : NPOracleProgram :=
  linkPrograms (bankCaseTwoSeedBlockListProgram occurrence)
    (targetBitProgram algorithm)

theorem bankCaseTwoTargetBitProgram_oracleFree
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    {occurrence : NPOracleProgram} (hoccurrence : OracleFree occurrence) :
    OracleFree (bankCaseTwoTargetBitProgram algorithm occurrence) :=
  oracleFree_linkPrograms
    (bankCaseTwoSeedBlockListProgram_oracleFree hoccurrence)
    (targetBitProgram_oracleFree algorithm)

def bankCaseTwoTargetBitFuel
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (occurrence : NPOracleProgram) (inputLength copies pointCode : ℕ)
    (occurrenceFuel : ℕ → ℕ) (bits : List Bool) : ℕ :=
  linkFuel (targetBitProgram algorithm)
    (bankCaseTwoSeedBlockListFuel occurrence inputLength copies pointCode
      occurrenceFuel)
    (targetBitCaseTwoFuel bits)

noncomputable def bankCaseTwoTargetBitBits
    (inputLength sourceLen width queryCount copies pointCode : ℕ)
    (occurrenceBits : ℕ → ℕ) (value : ℕ → Bool) (bits : List Bool) : ℕ :=
  occurrenceStageBits inputLength
    (bankCaseTwoSeedBlockListBits inputLength sourceLen width queryCount copies
      pointCode occurrenceBits value bits)
    (targetBitCaseTwoBits inputLength bits)

set_option maxHeartbeats 800000 in
-- The linked stage's fuel is a nested link term over the whole block loop.
/-- **Exact Case-2 execution from the numeral bank's frame.**  Modulo the
single per-block occurrence callee, one fixed oracle-free program returns the
XOR-amplified seed bit the Case-2 branch of the canonical target is defined
by, reading the copy count from the bank rather than from an immediate. -/
theorem run_bankCaseTwoTargetBitProgram
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
    (sourceLen width queryCount : ℕ)
    (occurrenceBits occurrenceFuel : ℕ → ℕ)
    (hoccurrence : ∀ block, block < copies →
      runNPOracleProgram occurrence (occurrenceBits block)
          (occurrenceFuel block)
          (initialNPOracleState target
            (Nat.pair block (encodeBitInput point))) =
        some
          (caseTwoScheduledBlockValue pcppSource caseTwo
            (encodeBitInput point) block).toNat) :
    runNPOracleProgram (bankCaseTwoTargetBitProgram algorithm occurrence)
        (bankCaseTwoTargetBitBits target sourceLen width queryCount copies
          (encodeBitInput point) occurrenceBits
          (caseTwoScheduledBlockValue pcppSource caseTwo
            (encodeBitInput point))
          ((List.range copies).map
            (caseTwoScheduledBlockValue pcppSource caseTwo
              (encodeBitInput point))))
        (bankCaseTwoTargetBitFuel algorithm occurrence target copies
          (encodeBitInput point) occurrenceFuel
          ((List.range copies).map
            (caseTwoScheduledBlockValue pcppSource caseTwo
              (encodeBitInput point))))
        (initialNPOracleState target
          (scheduleNumeralBankOutput sourceLen width queryCount copies
            (encodeBitInput point))) =
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
    (run_bankCaseTwoSeedBlockListProgram occurrence target sourceLen width
      queryCount copies (encodeBitInput point) occurrenceBits occurrenceFuel
      (caseTwoScheduledBlockValue pcppSource caseTwo (encodeBitInput point))
      hoccurrence)
    (run_targetBitProgram_caseTwo algorithm target
      ((List.range copies).map
        (caseTwoScheduledBlockValue pcppSource caseTwo
          (encodeBitInput point))))

/-! ## 4. The inverse schedule's Case-2 chain, from the bank's frame

On the diagonal — a request whose public length is the scheduled source length
the inverse chain works at — `BankScheduleDiagonal.publishedBankFrame_at_inverseDiagonal`
identifies the bank's frame with the chain's own numerals.  The copy register
is then literally the inverse schedule's XOR copy count, so §3 applies with no
schedule immediate anywhere in the stream.
-/

set_option maxHeartbeats 800000 in
-- The dispatched Case-2 envelopes are nested link terms.
/-- **The inverse schedule's Case-2 target bit, register-driven.**  Modulo the
per-block occurrence callee and the diagonal hypothesis, the composed program
returns exactly the canonical target of the inverse schedule from the numeral
bank's frame. -/
theorem run_bankCaseTwoTargetBitProgram_inverse
    (occurrence : NPOracleProgram)
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ)
    (hlarge :
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth) advantageExponent ≤
        target)
    (hyes :
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
        (sourceLength (inverseSourceIndex
          (inverseSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth)
            (inverseCoreAdvantagePower advantageExponent) target)))
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target))
    (hrejects :
      ¬machine.toSemantic.accepts
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target))
    (haccepts : ∀ caseTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent)))
        (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target),
      InverseCaseTwoAcceptance contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        (inverseCoreAdvantagePower advantageExponent)
        (inverseSelectedSource contracts
          (publishedHierarchyOuterPCP contracts clockDepth)
          (inverseCoreAdvantagePower advantageExponent) target)
        caseTwo machine)
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
      (inverseRefuterInput contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target))
    (hbranch :
      inverseTargetBranch contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target hyes = .caseTwo caseTwo)
    (hdiagonal :
      target =
        sourceLength (inverseSourceIndex
          (inverseSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth)
            (inverseCoreAdvantagePower advantageExponent) target)))
    (point : BitInput target) (occurrenceBits occurrenceFuel : ℕ → ℕ)
    (hoccurrence : ∀ block,
      block <
        inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (inverseBankRate contracts advantageExponent)
          (inverseSourceIndex
            (inverseSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              (inverseCoreAdvantagePower advantageExponent) target)) →
      runNPOracleProgram occurrence (occurrenceBits block)
          (occurrenceFuel block)
          (initialNPOracleState target
            (Nat.pair block (encodeBitInput point))) =
        some
          (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
            caseTwo (encodeBitInput point) block).toNat) :
    runNPOracleProgram
        (bankCaseTwoTargetBitProgram (publishedAmplifier contracts).algorithm
          occurrence)
        (bankCaseTwoTargetBitBits target
          (sourceLength (inverseSourceIndex
            (inverseSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              (inverseCoreAdvantagePower advantageExponent) target)))
          (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
            (inverseSourceIndex
              (inverseSelectedSource contracts
                (publishedHierarchyOuterPCP contracts clockDepth)
                (inverseCoreAdvantagePower advantageExponent) target)))
          ((publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
            (sourceLength (inverseSourceIndex
              (inverseSelectedSource contracts
                (publishedHierarchyOuterPCP contracts clockDepth)
                (inverseCoreAdvantagePower advantageExponent) target))))
          (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent)
            (inverseSourceIndex
              (inverseSelectedSource contracts
                (publishedHierarchyOuterPCP contracts clockDepth)
                (inverseCoreAdvantagePower advantageExponent) target)))
          (encodeBitInput point) occurrenceBits
          (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
            caseTwo (encodeBitInput point))
          ((List.range
            (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
              (publishedPointwisePCPP contracts)
              (inverseBankRate contracts advantageExponent)
              (inverseSourceIndex
                (inverseSelectedSource contracts
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (inverseCoreAdvantagePower advantageExponent) target)))).map
            (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
              caseTwo (encodeBitInput point))))
        (bankCaseTwoTargetBitFuel (publishedAmplifier contracts).algorithm
          occurrence target
          (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent)
            (inverseSourceIndex
              (inverseSelectedSource contracts
                (publishedHierarchyOuterPCP contracts clockDepth)
                (inverseCoreAdvantagePower advantageExponent) target)))
          (encodeBitInput point) occurrenceFuel
          ((List.range
            (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
              (publishedPointwisePCPP contracts)
              (inverseBankRate contracts advantageExponent)
              (inverseSourceIndex
                (inverseSelectedSource contracts
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (inverseCoreAdvantagePower advantageExponent) target)))).map
            (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
              caseTwo (encodeBitInput point))))
        (initialNPOracleState target
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) target
            (encodeBitInput point))) =
      some
        (inverseCanonicalTargetFunction contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target hlarge hyes hrejects haccepts point).toNat :=
  by
  rw [publishedBankFrame_at_inverseDiagonal contracts clockDepth
    advantageExponent target (encodeBitInput point) hdiagonal]
  rw [inverseCanonicalTargetFunction_caseTwo_apply contracts
    (publishedHierarchyOuterPCP contracts clockDepth) machine advantageExponent
    target hlarge hyes hrejects haccepts caseTwo hbranch point]
  exact run_bankCaseTwoTargetBitProgram
    (publishedAmplifier contracts).algorithm occurrence
    (publishedPointwisePCPP contracts) caseTwo point
    (inverseCaseTwoRawArity_le_target contracts
      (publishedHierarchyOuterPCP contracts clockDepth)
      (inverseCoreAdvantagePower advantageExponent) target
      (inverseCaseOneTargetOnset_ready contracts
        (publishedHierarchyOuterPCP contracts clockDepth) advantageExponent
        target hlarge).1)
    _ _ _ occurrenceBits occurrenceFuel hoccurrence

end NearCubicWires.BankCaseTwoSeedBlockListProgram
