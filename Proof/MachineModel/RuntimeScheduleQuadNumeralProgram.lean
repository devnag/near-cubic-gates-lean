import Proof.MachineModel.CanonicalRowCountExponentProgram
import Proof.MachineModel.RuntimeScheduleNumeralBank

namespace NearCubicWires.RuntimeScheduleQuadNumeralProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalRowCountExponentProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The straight-line frames

Each is a fixed instruction list with its own exact width, clock and
execution theorem.  Every width obligation below is `Nat.left_le_pair` or
`Nat.right_le_pair` against the frame's own input or output word. -/

private theorem le_pair_left {value left right : ℕ} (hvalue : value ≤ left) :
    value ≤ Nat.pair left right :=
  hvalue.trans (Nat.left_le_pair left right)

private theorem le_pair_right {value left right : ℕ} (hvalue : value ≤ right) :
    value ≤ Nat.pair left right :=
  hvalue.trans (Nat.right_le_pair left right)

/-- `pair left right ↦ left`. -/
def quadTakeLeftProgram : NPOracleProgram :=
  [ .unpairLeft 0 0 1
  , .halt 0
  ]

@[simp] theorem quadTakeLeftProgram_oracleFree :
    OracleFree quadTakeLeftProgram := by
  rfl

def quadTakeLeftBits (left right : ℕ) : ℕ :=
  natBitLength (Nat.pair left right)

theorem run_quadTakeLeftProgram (inputLength left right : ℕ) :
    runNPOracleProgram quadTakeLeftProgram (quadTakeLeftBits left right) 2
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some left := by
  have hleft : natBitLength left ≤ quadTakeLeftBits left right :=
    natBitLength_mono (Nat.left_le_pair _ _)
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := left) (by rfl) rfl
    (by simp [initialNPOracleState]) hleft]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hleft

/-- `pair left right ↦ pair left (pair left right)`. -/
def quadDupLeftProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .pair 2 0 0 2
  , .halt 0
  ]

@[simp] theorem quadDupLeftProgram_oracleFree :
    OracleFree quadDupLeftProgram := by
  rfl

def quadDupLeftBits (left right : ℕ) : ℕ :=
  natBitLength (Nat.pair left (Nat.pair left right))

theorem run_quadDupLeftProgram (inputLength left right : ℕ) :
    runNPOracleProgram quadDupLeftProgram (quadDupLeftBits left right) 3
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some (Nat.pair left (Nat.pair left right)) := by
  have houtput :
      natBitLength (Nat.pair left (Nat.pair left right)) ≤
        quadDupLeftBits left right := le_refl _
  have hleft : natBitLength left ≤ quadDupLeftBits left right :=
    natBitLength_mono (Nat.left_le_pair _ _)
  have hinput : natBitLength (Nat.pair left right) ≤ quadDupLeftBits left right :=
    natBitLength_mono (Nat.right_le_pair _ _)
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairLeft_instruction (value := left) (by rfl) rfl
    (by simp [initialNPOracleState]) hleft]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair left (Nat.pair left right))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 2. The clause-address envelope from the width register -/

/-- The published substituted-circuit size envelope, as numerals. -/
def substitutedSizeValue
    (requiredDegree sizeCoefficient substitutionExponent width : ℕ) : ℕ :=
  sizeCoefficient *
      (width + oracleSizeBound requiredDegree width + 1) ^ substitutionExponent +
    width

/-- The published clause-address envelope, as numerals. -/
def clauseBitsValue
    (requiredDegree sizeCoefficient substitutionExponent pcppCoefficient
      pcppDegree width : ℕ) : ℕ :=
  Nat.log 2 <|
    pcppCoefficient *
      (substitutedSizeValue requiredDegree sizeCoefficient substitutionExponent
          width + 1) ^
        pcppDegree

/-- The size envelope's leading summand: the substitution's own size bound at
the scheduled width and the small-oracle cap it induces. -/
def substitutedSizeCoreProgram
    (requiredDegree sizeCoefficient substitutionExponent : ℕ) :
    NPOracleProgram :=
  linkPrograms duplicateProgram <|
    linkPrograms (preserveRightProgram (pairIterProgram
        (oracleDepth requiredDegree))) <|
      linkPrograms addPairProgram <|
        linkPrograms (immediateAddProgram 1) <|
          linkPrograms (powProgram substitutionExponent)
            (immediateMulProgram sizeCoefficient)

theorem substitutedSizeCoreProgram_oracleFree
    (requiredDegree sizeCoefficient substitutionExponent : ℕ) :
    OracleFree
      (substitutedSizeCoreProgram requiredDegree sizeCoefficient
        substitutionExponent) :=
  oracleFree_linkPrograms duplicateProgram_oracleFree
    (oracleFree_linkPrograms
      (preserveRightProgram_oracleFree _
        (pairIterProgram_oracleFree (oracleDepth requiredDegree)))
      (oracleFree_linkPrograms addPairProgram_oracleFree
        (oracleFree_linkPrograms (immediateAddProgram_oracleFree 1)
          (oracleFree_linkPrograms
            (powProgram_oracleFree substitutionExponent)
            (immediateMulProgram_oracleFree sizeCoefficient)))))

/-- The size envelope's leading summand, as a numeral. -/
def substitutedSizeCoreValue
    (requiredDegree sizeCoefficient substitutionExponent width : ℕ) : ℕ :=
  sizeCoefficient *
    (oracleSizeBound requiredDegree width + width + 1) ^ substitutionExponent

def substitutedSizeCoreFuel
    (requiredDegree sizeCoefficient substitutionExponent width : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (preserveRightProgram (pairIterProgram
        (oracleDepth requiredDegree)))
      (linkPrograms addPairProgram
        (linkPrograms (immediateAddProgram 1)
          (linkPrograms (powProgram substitutionExponent)
            (immediateMulProgram sizeCoefficient)))))
    2 <|
    linkFuel
      (linkPrograms addPairProgram
        (linkPrograms (immediateAddProgram 1)
          (linkPrograms (powProgram substitutionExponent)
            (immediateMulProgram sizeCoefficient))))
      (preserveRightFuel (pairIterFuel (oracleDepth requiredDegree))) <|
      linkFuel
        (linkPrograms (immediateAddProgram 1)
          (linkPrograms (powProgram substitutionExponent)
            (immediateMulProgram sizeCoefficient)))
        4 <|
        linkFuel
          (linkPrograms (powProgram substitutionExponent)
            (immediateMulProgram sizeCoefficient))
          3 <|
          linkFuel (immediateMulProgram sizeCoefficient)
            (powFuel substitutionExponent
              (oracleSizeBound requiredDegree width + width + 1))
            (immediateMulFuel
              ((oracleSizeBound requiredDegree width + width + 1) ^
                substitutionExponent))

def substitutedSizeCoreBits
    (inputLength requiredDegree sizeCoefficient substitutionExponent
      width : ℕ) : ℕ :=
  occurrenceStageBits inputLength (duplicateBits width) <|
    occurrenceStageBits inputLength
      (preserveRightBits
        (pairIterBits inputLength (oracleDepth requiredDegree) width) width
        width (oracleSizeBound requiredDegree width)) <|
      occurrenceStageBits inputLength
        (addPairBits (oracleSizeBound requiredDegree width) width) <|
        occurrenceStageBits inputLength
          (immediateAddBits 1 (oracleSizeBound requiredDegree width + width)) <|
          occurrenceStageBits inputLength
            (powBits inputLength substitutionExponent
              (oracleSizeBound requiredDegree width + width + 1))
            (immediateMulBits inputLength sizeCoefficient
              ((oracleSizeBound requiredDegree width + width + 1) ^
                substitutionExponent))

/-- **The size envelope's leading summand, executed.** -/
theorem run_substitutedSizeCoreProgram
    (inputLength requiredDegree sizeCoefficient substitutionExponent
      width : ℕ) :
    runNPOracleProgram
        (substitutedSizeCoreProgram requiredDegree sizeCoefficient
          substitutionExponent)
        (substitutedSizeCoreBits inputLength requiredDegree sizeCoefficient
          substitutionExponent width)
        (substitutedSizeCoreFuel requiredDegree sizeCoefficient
          substitutionExponent width)
        (initialNPOracleState inputLength width) =
      some
        (substitutedSizeCoreValue requiredDegree sizeCoefficient
          substitutionExponent width) :=
  run_occurrenceStage (run_duplicateProgram inputLength width)
    (run_occurrenceStage
      (run_preserveRightProgram (pairIterProgram (oracleDepth requiredDegree))
        inputLength (pairIterBits inputLength (oracleDepth requiredDegree) width)
        (pairIterFuel (oracleDepth requiredDegree)) width width
        (oracleSizeBound requiredDegree width)
        (run_pairIterProgram_pairClock inputLength (oracleDepth requiredDegree)
          width))
      (run_occurrenceStage
        (run_addPairProgram inputLength
          (oracleSizeBound requiredDegree width) width)
        (run_occurrenceStage
          (run_immediateAddProgram inputLength 1
            (oracleSizeBound requiredDegree width + width))
          (run_occurrenceStage
            (run_powProgram inputLength substitutionExponent
              (oracleSizeBound requiredDegree width + width + 1))
            (run_immediateMulProgram inputLength sizeCoefficient
              ((oracleSizeBound requiredDegree width + width + 1) ^
                substitutionExponent))))))

/-- The clause-address envelope from the scheduled width. -/
def clauseBitsCoreProgram
    (requiredDegree sizeCoefficient substitutionExponent pcppCoefficient
      pcppDegree : ℕ) : NPOracleProgram :=
  linkPrograms duplicateProgram <|
    linkPrograms (preserveRightProgram
        (substitutedSizeCoreProgram requiredDegree sizeCoefficient
          substitutionExponent)) <|
      linkPrograms addPairProgram <|
        linkPrograms (immediateAddProgram 1) <|
          linkPrograms (powProgram pcppDegree) <|
            linkPrograms (immediateMulProgram pcppCoefficient) floorLogProgram

theorem clauseBitsCoreProgram_oracleFree
    (requiredDegree sizeCoefficient substitutionExponent pcppCoefficient
      pcppDegree : ℕ) :
    OracleFree
      (clauseBitsCoreProgram requiredDegree sizeCoefficient substitutionExponent
        pcppCoefficient pcppDegree) :=
  oracleFree_linkPrograms duplicateProgram_oracleFree
    (oracleFree_linkPrograms
      (preserveRightProgram_oracleFree _
        (substitutedSizeCoreProgram_oracleFree requiredDegree sizeCoefficient
          substitutionExponent))
      (oracleFree_linkPrograms addPairProgram_oracleFree
        (oracleFree_linkPrograms (immediateAddProgram_oracleFree 1)
          (oracleFree_linkPrograms (powProgram_oracleFree pcppDegree)
            (oracleFree_linkPrograms
              (immediateMulProgram_oracleFree pcppCoefficient)
              floorLogProgram_oracleFree)))))

def clauseBitsCoreFuel
    (requiredDegree sizeCoefficient substitutionExponent pcppCoefficient
      pcppDegree width : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (preserveRightProgram
        (substitutedSizeCoreProgram requiredDegree sizeCoefficient
          substitutionExponent))
      (linkPrograms addPairProgram
        (linkPrograms (immediateAddProgram 1)
          (linkPrograms (powProgram pcppDegree)
            (linkPrograms (immediateMulProgram pcppCoefficient)
              floorLogProgram)))))
    2 <|
    linkFuel
      (linkPrograms addPairProgram
        (linkPrograms (immediateAddProgram 1)
          (linkPrograms (powProgram pcppDegree)
            (linkPrograms (immediateMulProgram pcppCoefficient)
              floorLogProgram))))
      (preserveRightFuel
        (substitutedSizeCoreFuel requiredDegree sizeCoefficient
          substitutionExponent width)) <|
      linkFuel
        (linkPrograms (immediateAddProgram 1)
          (linkPrograms (powProgram pcppDegree)
            (linkPrograms (immediateMulProgram pcppCoefficient)
              floorLogProgram)))
        4 <|
        linkFuel
          (linkPrograms (powProgram pcppDegree)
            (linkPrograms (immediateMulProgram pcppCoefficient)
              floorLogProgram))
          3 <|
          linkFuel
            (linkPrograms (immediateMulProgram pcppCoefficient) floorLogProgram)
            (powFuel pcppDegree
              (substitutedSizeValue requiredDegree sizeCoefficient
                substitutionExponent width + 1)) <|
            linkFuel floorLogProgram
              (immediateMulFuel
                ((substitutedSizeValue requiredDegree sizeCoefficient
                  substitutionExponent width + 1) ^ pcppDegree))
              (floorLogFuel
                (pcppCoefficient *
                  (substitutedSizeValue requiredDegree sizeCoefficient
                    substitutionExponent width + 1) ^ pcppDegree))

def clauseBitsCoreBits
    (inputLength requiredDegree sizeCoefficient substitutionExponent
      pcppCoefficient pcppDegree width : ℕ) : ℕ :=
  occurrenceStageBits inputLength (duplicateBits width) <|
    occurrenceStageBits inputLength
      (preserveRightBits
        (substitutedSizeCoreBits inputLength requiredDegree sizeCoefficient
          substitutionExponent width)
        width width
        (substitutedSizeCoreValue requiredDegree sizeCoefficient
          substitutionExponent width)) <|
      occurrenceStageBits inputLength
        (addPairBits
          (substitutedSizeCoreValue requiredDegree sizeCoefficient
            substitutionExponent width)
          width) <|
        occurrenceStageBits inputLength
          (immediateAddBits 1
            (substitutedSizeValue requiredDegree sizeCoefficient
              substitutionExponent width)) <|
          occurrenceStageBits inputLength
            (powBits inputLength pcppDegree
              (substitutedSizeValue requiredDegree sizeCoefficient
                substitutionExponent width + 1)) <|
            occurrenceStageBits inputLength
              (immediateMulBits inputLength pcppCoefficient
                ((substitutedSizeValue requiredDegree sizeCoefficient
                  substitutionExponent width + 1) ^ pcppDegree))
              (floorLogBits inputLength
                (pcppCoefficient *
                  (substitutedSizeValue requiredDegree sizeCoefficient
                    substitutionExponent width + 1) ^ pcppDegree))

/-- **The clause-address envelope, executed.**  The only side condition is the
published pointwise source's coefficient positivity. -/
theorem run_clauseBitsCoreProgram
    (inputLength requiredDegree sizeCoefficient substitutionExponent
      pcppCoefficient pcppDegree width : ℕ)
    (hcoefficient : 1 ≤ pcppCoefficient) :
    runNPOracleProgram
        (clauseBitsCoreProgram requiredDegree sizeCoefficient
          substitutionExponent pcppCoefficient pcppDegree)
        (clauseBitsCoreBits inputLength requiredDegree sizeCoefficient
          substitutionExponent pcppCoefficient pcppDegree width)
        (clauseBitsCoreFuel requiredDegree sizeCoefficient substitutionExponent
          pcppCoefficient pcppDegree width)
        (initialNPOracleState inputLength width) =
      some
        (clauseBitsValue requiredDegree sizeCoefficient substitutionExponent
          pcppCoefficient pcppDegree width) := by
  have hsum :
      substitutedSizeCoreValue requiredDegree sizeCoefficient
            substitutionExponent width + width =
        substitutedSizeValue requiredDegree sizeCoefficient substitutionExponent
          width := by
    rw [substitutedSizeCoreValue, substitutedSizeValue,
      Nat.add_comm (oracleSizeBound requiredDegree width) width]
  have hpositive :
      1 ≤
        pcppCoefficient *
          (substitutedSizeValue requiredDegree sizeCoefficient
            substitutionExponent width + 1) ^ pcppDegree := by
    have hpower :
        1 ≤
          (substitutedSizeValue requiredDegree sizeCoefficient
            substitutionExponent width + 1) ^ pcppDegree :=
      Nat.one_le_pow _ _ (by omega)
    calc
      1 = 1 * 1 := by omega
      _ ≤ pcppCoefficient *
            (substitutedSizeValue requiredDegree sizeCoefficient
              substitutionExponent width + 1) ^ pcppDegree :=
        Nat.mul_le_mul hcoefficient hpower
  have hrun :
      runNPOracleProgram
          (clauseBitsCoreProgram requiredDegree sizeCoefficient
            substitutionExponent pcppCoefficient pcppDegree)
          (clauseBitsCoreBits inputLength requiredDegree sizeCoefficient
            substitutionExponent pcppCoefficient pcppDegree width)
          (clauseBitsCoreFuel requiredDegree sizeCoefficient
            substitutionExponent pcppCoefficient pcppDegree width)
          (initialNPOracleState inputLength width) =
        some
          (Nat.log 2
            (pcppCoefficient *
              (substitutedSizeValue requiredDegree sizeCoefficient
                substitutionExponent width + 1) ^ pcppDegree)) := by
    refine run_occurrenceStage (run_duplicateProgram inputLength width) ?_
    refine run_occurrenceStage
      (run_preserveRightProgram
        (substitutedSizeCoreProgram requiredDegree sizeCoefficient
          substitutionExponent)
        inputLength
        (substitutedSizeCoreBits inputLength requiredDegree sizeCoefficient
          substitutionExponent width)
        (substitutedSizeCoreFuel requiredDegree sizeCoefficient
          substitutionExponent width)
        width width
        (substitutedSizeCoreValue requiredDegree sizeCoefficient
          substitutionExponent width)
        (run_substitutedSizeCoreProgram inputLength requiredDegree
          sizeCoefficient substitutionExponent width)) ?_
    have hadd :=
      run_addPairProgram inputLength
        (substitutedSizeCoreValue requiredDegree sizeCoefficient
          substitutionExponent width) width
    rw [hsum] at hadd
    refine run_occurrenceStage hadd ?_
    refine run_occurrenceStage
      (run_immediateAddProgram inputLength 1
        (substitutedSizeValue requiredDegree sizeCoefficient
          substitutionExponent width)) ?_
    refine run_occurrenceStage
      (run_powProgram inputLength pcppDegree
        (substitutedSizeValue requiredDegree sizeCoefficient
          substitutionExponent width + 1)) ?_
    exact run_occurrenceStage
      (run_immediateMulProgram inputLength pcppCoefficient
        ((substitutedSizeValue requiredDegree sizeCoefficient
          substitutionExponent width + 1) ^ pcppDegree))
      (run_floorLogProgram inputLength
        (pcppCoefficient *
          (substitutedSizeValue requiredDegree sizeCoefficient
            substitutionExponent width + 1) ^ pcppDegree)
        hpositive)
  exact hrun

/-! ## 3. The outer native width from the published shape runner -/

/-- The outer native width: one call of the published shape runner at the
scheduled length, then its left component. -/
def nativeWidthProgram (shapeProgram : NPOracleProgram) : NPOracleProgram :=
  linkPrograms shapeProgram quadTakeLeftProgram

theorem nativeWidthProgram_oracleFree
    {shapeProgram : NPOracleProgram} (hshape : OracleFree shapeProgram) :
    OracleFree (nativeWidthProgram shapeProgram) :=
  oracleFree_linkPrograms hshape quadTakeLeftProgram_oracleFree

def nativeWidthFuel (shapeFuel : ℕ) : ℕ :=
  linkFuel quadTakeLeftProgram shapeFuel 2

def nativeWidthBits (inputLength shapeBits shapeCode : ℕ) : ℕ :=
  occurrenceStageBits inputLength shapeBits
    (quadTakeLeftBits (Nat.unpair shapeCode).1 (Nat.unpair shapeCode).2)

/-- **The native width, executed.**  The shape runner's own execution is the
only hypothesis. -/
theorem run_nativeWidthProgram (shapeProgram : NPOracleProgram)
    (inputLength shapeBits shapeFuel shapeCode : ℕ)
    (hshape :
      runNPOracleProgram shapeProgram shapeBits shapeFuel
          (initialNPOracleState inputLength inputLength) = some shapeCode) :
    runNPOracleProgram (nativeWidthProgram shapeProgram)
        (nativeWidthBits inputLength shapeBits shapeCode)
        (nativeWidthFuel shapeFuel)
        (initialNPOracleState inputLength inputLength) =
      some (Nat.unpair shapeCode).1 := by
  have htake :=
    run_quadTakeLeftProgram inputLength (Nat.unpair shapeCode).1
      (Nat.unpair shapeCode).2
  rw [Nat.pair_unpair] at htake
  exact run_occurrenceStage hshape htake

/-! ## 4. The quad word -/

/-- The schedule half of the occurrence packet: the four numerals of
`RuntimeCaseTwoBlockOccurrenceProgram.occurrencePacket` that do not mention the
recovered oracle. -/
def occurrenceQuadWord
    (arity inputArity paddedInputBits paddedClauseBits : ℕ) : ℕ :=
  Nat.pair arity (Nat.pair inputArity (Nat.pair paddedInputBits
    paddedClauseBits))

/-- `pair clauseBits (pair width nativeWidth) ↦ the quad word`.  The seed arity
is the one addition: `widthEnvelope + clauseBitsEnvelope + 1`. -/
def quadAssembleProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .add 4 2 6 5
  , .increment 6 6
  , .pair 4 2 7 7
  , .pair 5 7 8 8
  , .pair 6 8 0 9
  , .halt 0
  ]

@[simp] theorem quadAssembleProgram_oracleFree :
    OracleFree quadAssembleProgram := by
  rfl

def quadAssembleInput (clauseBits width nativeWidth : ℕ) : ℕ :=
  Nat.pair clauseBits (Nat.pair width nativeWidth)

def quadAssembleBits (clauseBits width nativeWidth : ℕ) : ℕ :=
  natBitLength
    (max (quadAssembleInput clauseBits width nativeWidth)
      (occurrenceQuadWord (width + clauseBits + 1) nativeWidth width
        clauseBits))

theorem run_quadAssembleProgram
    (inputLength clauseBits width nativeWidth : ℕ) :
    runNPOracleProgram quadAssembleProgram
        (quadAssembleBits clauseBits width nativeWidth) 10
        (initialNPOracleState inputLength
          (quadAssembleInput clauseBits width nativeWidth)) =
      some
        (occurrenceQuadWord (width + clauseBits + 1) nativeWidth width
          clauseBits) := by
  have hinput : ∀ value : ℕ,
      value ≤ quadAssembleInput clauseBits width nativeWidth →
      natBitLength value ≤ quadAssembleBits clauseBits width nativeWidth :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have houtput : ∀ value : ℕ,
      value ≤
        occurrenceQuadWord (width + clauseBits + 1) nativeWidth width
          clauseBits →
      natBitLength value ≤ quadAssembleBits clauseBits width nativeWidth :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hclause := hinput clauseBits (Nat.left_le_pair _ _)
  have hinner :=
    hinput (Nat.pair width nativeWidth) (Nat.right_le_pair _ _)
  have hwidth :=
    hinput width (le_pair_right (Nat.left_le_pair _ _))
  have hnative :=
    hinput nativeWidth (le_pair_right (Nat.right_le_pair _ _))
  have harity :=
    houtput (width + clauseBits + 1) (Nat.left_le_pair _ _)
  have hsum : natBitLength (width + clauseBits) ≤
      quadAssembleBits clauseBits width nativeWidth :=
    (natBitLength_mono (by omega)).trans harity
  have hpairLow :=
    houtput (Nat.pair width clauseBits)
      (le_pair_right (le_pair_right (le_refl _)))
  have hpairMid :=
    houtput (Nat.pair nativeWidth (Nat.pair width clauseBits))
      (le_pair_right (le_refl _))
  have hfinal := houtput _ (le_refl _)
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairLeft_instruction (value := clauseBits) (by rfl) rfl
    (by simp [initialNPOracleState, quadAssembleInput]) hclause]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair width nativeWidth)
    (by rfl) rfl
    (by simp [initialNPOracleState, quadAssembleInput, NPOracleState.write,
      NPOracleState.jump]) hinner]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := width) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidth]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := nativeWidth) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnative]
  rw [show 6 = 5 + 1 by omega]
  rw [run_add_instruction (value := width + clauseBits) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsum]
  rw [show 5 = 4 + 1 by omega]
  rw [run_increment_instruction (value := width + clauseBits + 1) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) harity]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair width clauseBits) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hpairLow]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair nativeWidth (Nat.pair width clauseBits)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hpairMid]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      occurrenceQuadWord (width + clauseBits + 1) nativeWidth width clauseBits)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, occurrenceQuadWord])
    hfinal]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfinal

/-- **The schedule quad as one fixed stream.**  Every parameter is frozen: the
pairing-clock depth, the published shape coefficient and proof exponent, the
substitution's size coefficient and exponent, the pointwise source's
coefficient and degree, the requested polynomial degree, and the published
shape runner. -/
def occurrenceQuadProgram (shapeProgram : NPOracleProgram)
    (clockDepth coefficient exponent requiredDegree sizeCoefficient
      substitutionExponent pcppCoefficient pcppDegree : ℕ) : NPOracleProgram :=
  linkPrograms duplicateProgram <|
    linkPrograms (preserveRightProgram
        (widthEnvelopeProgram clockDepth coefficient exponent)) <|
      linkPrograms swapPairProgram <|
        linkPrograms (preserveRightProgram (nativeWidthProgram shapeProgram)) <|
          linkPrograms swapPairProgram <|
            linkPrograms quadDupLeftProgram <|
              linkPrograms (preserveRightProgram
                  (clauseBitsCoreProgram requiredDegree sizeCoefficient
                    substitutionExponent pcppCoefficient pcppDegree))
                quadAssembleProgram

theorem occurrenceQuadProgram_oracleFree
    {shapeProgram : NPOracleProgram}
    (clockDepth coefficient exponent requiredDegree sizeCoefficient
      substitutionExponent pcppCoefficient pcppDegree : ℕ)
    (hshape : OracleFree shapeProgram) :
    OracleFree
      (occurrenceQuadProgram shapeProgram clockDepth coefficient exponent
        requiredDegree sizeCoefficient substitutionExponent pcppCoefficient
        pcppDegree) :=
  oracleFree_linkPrograms duplicateProgram_oracleFree
    (oracleFree_linkPrograms
      (preserveRightProgram_oracleFree _
        (widthEnvelopeProgram_oracleFree clockDepth coefficient exponent))
      (oracleFree_linkPrograms swapPairProgram_oracleFree
        (oracleFree_linkPrograms
          (preserveRightProgram_oracleFree _
            (nativeWidthProgram_oracleFree hshape))
          (oracleFree_linkPrograms swapPairProgram_oracleFree
            (oracleFree_linkPrograms quadDupLeftProgram_oracleFree
              (oracleFree_linkPrograms
                (preserveRightProgram_oracleFree _
                  (clauseBitsCoreProgram_oracleFree requiredDegree
                    sizeCoefficient substitutionExponent pcppCoefficient
                    pcppDegree))
                quadAssembleProgram_oracleFree))))))

def occurrenceQuadFuel (shapeProgram : NPOracleProgram)
    (clockDepth coefficient exponent requiredDegree sizeCoefficient
      substitutionExponent pcppCoefficient pcppDegree sourceLen
      shapeFuel : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (preserveRightProgram
        (widthEnvelopeProgram clockDepth coefficient exponent))
      (linkPrograms swapPairProgram
        (linkPrograms (preserveRightProgram (nativeWidthProgram shapeProgram))
          (linkPrograms swapPairProgram
            (linkPrograms quadDupLeftProgram
              (linkPrograms (preserveRightProgram
                  (clauseBitsCoreProgram requiredDegree sizeCoefficient
                    substitutionExponent pcppCoefficient pcppDegree))
                quadAssembleProgram))))))
    2 <|
    linkFuel
      (linkPrograms swapPairProgram
        (linkPrograms (preserveRightProgram (nativeWidthProgram shapeProgram))
          (linkPrograms swapPairProgram
            (linkPrograms quadDupLeftProgram
              (linkPrograms (preserveRightProgram
                  (clauseBitsCoreProgram requiredDegree sizeCoefficient
                    substitutionExponent pcppCoefficient pcppDegree))
                quadAssembleProgram)))))
      (preserveRightFuel
        (widthEnvelopeFuel clockDepth coefficient exponent sourceLen)) <|
      linkFuel
        (linkPrograms (preserveRightProgram (nativeWidthProgram shapeProgram))
          (linkPrograms swapPairProgram
            (linkPrograms quadDupLeftProgram
              (linkPrograms (preserveRightProgram
                  (clauseBitsCoreProgram requiredDegree sizeCoefficient
                    substitutionExponent pcppCoefficient pcppDegree))
                quadAssembleProgram))))
        4 <|
        linkFuel
          (linkPrograms swapPairProgram
            (linkPrograms quadDupLeftProgram
              (linkPrograms (preserveRightProgram
                  (clauseBitsCoreProgram requiredDegree sizeCoefficient
                    substitutionExponent pcppCoefficient pcppDegree))
                quadAssembleProgram)))
          (preserveRightFuel (nativeWidthFuel shapeFuel)) <|
          linkFuel
            (linkPrograms quadDupLeftProgram
              (linkPrograms (preserveRightProgram
                  (clauseBitsCoreProgram requiredDegree sizeCoefficient
                    substitutionExponent pcppCoefficient pcppDegree))
                quadAssembleProgram))
            4 <|
            linkFuel
              (linkPrograms (preserveRightProgram
                  (clauseBitsCoreProgram requiredDegree sizeCoefficient
                    substitutionExponent pcppCoefficient pcppDegree))
                quadAssembleProgram)
              3 <|
              linkFuel quadAssembleProgram
                (preserveRightFuel
                  (clauseBitsCoreFuel requiredDegree sizeCoefficient
                    substitutionExponent pcppCoefficient pcppDegree
                    (widthValue clockDepth coefficient exponent sourceLen)))
                10

def occurrenceQuadBits
    (inputLength clockDepth coefficient exponent requiredDegree sizeCoefficient
      substitutionExponent pcppCoefficient pcppDegree sourceLen shapeBits
      shapeCode : ℕ) : ℕ :=
  let width := widthValue clockDepth coefficient exponent sourceLen
  let nativeWidth := (Nat.unpair shapeCode).1
  let clauseBits :=
    clauseBitsValue requiredDegree sizeCoefficient substitutionExponent
      pcppCoefficient pcppDegree width
  occurrenceStageBits inputLength (duplicateBits sourceLen) <|
    occurrenceStageBits inputLength
      (preserveRightBits
        (widthEnvelopeBits inputLength clockDepth coefficient exponent sourceLen)
        sourceLen sourceLen width) <|
      occurrenceStageBits inputLength (swapPairBits width sourceLen) <|
        occurrenceStageBits inputLength
          (preserveRightBits
            (nativeWidthBits inputLength shapeBits shapeCode) sourceLen width
            nativeWidth) <|
          occurrenceStageBits inputLength (swapPairBits nativeWidth width) <|
            occurrenceStageBits inputLength
              (quadDupLeftBits width nativeWidth) <|
              occurrenceStageBits inputLength
                (preserveRightBits
                  (clauseBitsCoreBits inputLength requiredDegree sizeCoefficient
                    substitutionExponent pcppCoefficient pcppDegree width)
                  width (Nat.pair width nativeWidth) clauseBits)
                (quadAssembleBits clauseBits width nativeWidth)

set_option maxHeartbeats 800000 in
-- Seven linked stages with three `preserveRight` frames, so the width and clock
-- expressions of the statement alone exceed the default budget.
/-- **The schedule quad, executed.**  From the scheduled source length in both
registers the stream emits the quad word of the occurrence packet.  The two
side conditions are the published width budget's positivity and the pointwise
source's coefficient positivity; the shape runner's own execution is the single
imported hypothesis. -/
theorem run_occurrenceQuadProgram (shapeProgram : NPOracleProgram)
    (sourceLen clockDepth coefficient exponent requiredDegree sizeCoefficient
      substitutionExponent pcppCoefficient pcppDegree shapeBits shapeFuel
      shapeCode : ℕ)
    (hbudget : 1 ≤ widthBudgetValue clockDepth coefficient exponent sourceLen)
    (hcoefficient : 1 ≤ pcppCoefficient)
    (hshape :
      runNPOracleProgram shapeProgram shapeBits shapeFuel
          (initialNPOracleState sourceLen sourceLen) = some shapeCode) :
    runNPOracleProgram
        (occurrenceQuadProgram shapeProgram clockDepth coefficient exponent
          requiredDegree sizeCoefficient substitutionExponent pcppCoefficient
          pcppDegree)
        (occurrenceQuadBits sourceLen clockDepth coefficient
          exponent requiredDegree sizeCoefficient substitutionExponent
          pcppCoefficient pcppDegree sourceLen shapeBits shapeCode)
        (occurrenceQuadFuel shapeProgram clockDepth coefficient exponent
          requiredDegree sizeCoefficient substitutionExponent pcppCoefficient
          pcppDegree sourceLen shapeFuel)
        (initialNPOracleState sourceLen sourceLen) =
      some
        (occurrenceQuadWord
          (widthValue clockDepth coefficient exponent sourceLen +
            clauseBitsValue requiredDegree sizeCoefficient substitutionExponent
              pcppCoefficient pcppDegree
              (widthValue clockDepth coefficient exponent sourceLen) + 1)
          (Nat.unpair shapeCode).1
          (widthValue clockDepth coefficient exponent sourceLen)
          (clauseBitsValue requiredDegree sizeCoefficient substitutionExponent
            pcppCoefficient pcppDegree
            (widthValue clockDepth coefficient exponent sourceLen))) := by
  refine run_occurrenceStage (run_duplicateProgram sourceLen sourceLen) ?_
  refine run_occurrenceStage
    (run_preserveRightProgram (widthEnvelopeProgram clockDepth coefficient
        exponent) sourceLen
      (widthEnvelopeBits sourceLen clockDepth coefficient exponent sourceLen)
      (widthEnvelopeFuel clockDepth coefficient exponent sourceLen) sourceLen
      sourceLen (widthValue clockDepth coefficient exponent sourceLen)
      (run_widthEnvelopeProgram sourceLen clockDepth coefficient exponent
        sourceLen hbudget)) ?_
  refine run_occurrenceStage
    (run_swapPairProgram sourceLen
      (widthValue clockDepth coefficient exponent sourceLen) sourceLen) ?_
  refine run_occurrenceStage
    (run_preserveRightProgram (nativeWidthProgram shapeProgram) sourceLen
      (nativeWidthBits sourceLen shapeBits shapeCode) (nativeWidthFuel shapeFuel)
      sourceLen (widthValue clockDepth coefficient exponent sourceLen)
      (Nat.unpair shapeCode).1
      (run_nativeWidthProgram shapeProgram sourceLen shapeBits shapeFuel
        shapeCode hshape)) ?_
  refine run_occurrenceStage
    (run_swapPairProgram sourceLen (Nat.unpair shapeCode).1
      (widthValue clockDepth coefficient exponent sourceLen)) ?_
  refine run_occurrenceStage
    (run_quadDupLeftProgram sourceLen
      (widthValue clockDepth coefficient exponent sourceLen)
      (Nat.unpair shapeCode).1) ?_
  exact run_occurrenceStage
    (run_preserveRightProgram
      (clauseBitsCoreProgram requiredDegree sizeCoefficient substitutionExponent
        pcppCoefficient pcppDegree)
      sourceLen
      (clauseBitsCoreBits sourceLen requiredDegree sizeCoefficient
        substitutionExponent pcppCoefficient pcppDegree
        (widthValue clockDepth coefficient exponent sourceLen))
      (clauseBitsCoreFuel requiredDegree sizeCoefficient substitutionExponent
        pcppCoefficient pcppDegree
        (widthValue clockDepth coefficient exponent sourceLen))
      (widthValue clockDepth coefficient exponent sourceLen)
      (Nat.pair (widthValue clockDepth coefficient exponent sourceLen)
        (Nat.unpair shapeCode).1)
      (clauseBitsValue requiredDegree sizeCoefficient substitutionExponent
        pcppCoefficient pcppDegree
        (widthValue clockDepth coefficient exponent sourceLen))
      (run_clauseBitsCoreProgram sourceLen requiredDegree sizeCoefficient
        substitutionExponent pcppCoefficient pcppDegree
        (widthValue clockDepth coefficient exponent sourceLen) hcoefficient))
    (run_quadAssembleProgram sourceLen
      (clauseBitsValue requiredDegree sizeCoefficient substitutionExponent
        pcppCoefficient pcppDegree
        (widthValue clockDepth coefficient exponent sourceLen))
      (widthValue clockDepth coefficient exponent sourceLen)
      (Nat.unpair shapeCode).1)

/-! ## 5. The published identifications

Each numeral the stream emits is *definitionally* the published envelope at the
scheduled length; the seed arity is the one identity that needs a rewrite. -/

/-- The stream's size numeral is the published substituted-circuit size
envelope. -/
theorem substitutedSizeValue_eq_envelope
    {depth : ℕ}
    {source : ExecutableRefuterSource (pairClock depth)}
    (outer : HierarchyOuterPCP source) (requiredDegree sourceLen : ℕ) :
    substitutedSizeValue requiredDegree outer.substitution.sizeCoefficient
        outer.substitutionExponent (widthEnvelope outer sourceLen) =
      substitutedCircuitSizeEnvelope outer (oracleSizeBound requiredDegree)
        sourceLen :=
  rfl

/-- The stream's clause numeral is the published clause-address envelope. -/
theorem clauseBitsValue_eq_envelope
    {depth : ℕ}
    {source : ExecutableRefuterSource (pairClock depth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree sourceLen : ℕ) :
    clauseBitsValue requiredDegree outer.substitution.sizeCoefficient
        outer.substitutionExponent pcppSource.coefficient pcppSource.degree
        (widthEnvelope outer sourceLen) =
      clauseBitsEnvelope outer pcppSource (oracleSizeBound requiredDegree)
        sourceLen :=
  rfl

/-- The stream's arity numeral is the published seed arity: the seed's clause
address width is the clause envelope at the scheduled length, so no third
computation is needed. -/
theorem seedArity_eq_sum
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree sourceIndex : ℕ) :
    seedArity outer pcppSource requiredDegree sourceIndex =
      widthEnvelope outer (sourceLength sourceIndex) +
        clauseBitsEnvelope outer pcppSource (oracleSizeBound requiredDegree)
          (sourceLength sourceIndex) + 1 := by
  rw [seedArity, scheduledWidth,
    scheduledClauseBits_eq_envelope outer pcppSource requiredDegree sourceIndex]

end NearCubicWires.RuntimeScheduleQuadNumeralProgram
