import Proof.Circuits.CanonicalBalancedCall
import Proof.Circuits.VerifiedPlaneRequestBuilder
import Proof.Foundations.VerifiedLinker

/-!
# Width-safe signed-plane rectangular calls

The signed-plane printer makes a variable number of calls to the published
rectangular-product program.  This module fixes the production call ABI to the
canonical balanced list representation; neither requests nor outputs pass
through the legacy linked-list accumulator.
-/

namespace NearCubicWires.CanonicalSignedPlaneCall

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPrinter
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedPlaneRequestBuilder
open NearCubicWires.VerifiedLinker

/-- Total matrix view used only after the public dimension has been decoded.
Canonical request codes round-trip exactly; malformed codes acquire the
all-false padding already used by the other total executable decoders. -/
def bitMatrixOfCode (rows columns code : ℕ) : BitMatrix rows columns :=
  let values := (decodeBalancedList code).getD []
  fun row column =>
    values.getD (row.val * columns + column.val) 0 != 0

private theorem matrixEntries_getElem?
    {α : Type} {rows columns : ℕ}
    (matrix : Fin rows → Fin columns → α)
    (row : Fin rows) (column : Fin columns) :
    (List.ofFn fun r => List.ofFn fun c => matrix r c).flatten[
        row.val * columns + column.val]? =
      some (matrix row column) := by
  induction rows with
  | zero => exact Fin.elim0 row
  | succ rows ih =>
      refine Fin.cases ?_ (fun predecessor => ?_) row
      · rw [List.ofFn_succ, List.flatten_cons, List.getElem?_append]
        simp [column.isLt]
      · rw [List.ofFn_succ, List.flatten_cons, List.getElem?_append]
        simp only [List.length_ofFn, Fin.val_succ, Nat.add_mul]
        rw [if_neg (by omega)]
        have hindex :
            predecessor.val * columns + 1 * columns + column.val - columns =
              predecessor.val * columns + column.val := by
          omega
        rw [hindex]
        exact ih (fun r c => matrix r.succ c) predecessor

@[simp] theorem bitMatrixOfCode_encodeBitMatrix
    {rows columns : ℕ} (matrix : BitMatrix rows columns) :
    bitMatrixOfCode rows columns (encodeBitMatrix matrix) = matrix := by
  funext row column
  rw [show bitMatrixOfCode rows columns (encodeBitMatrix matrix) row column =
      ((bitMatrixEntries matrix)[row.val * columns + column.val]?.getD 0 != 0)
    by simp [bitMatrixOfCode, encodeBitMatrix]]
  rw [show (bitMatrixEntries matrix)[row.val * columns + column.val]? =
      some (matrix row column).toNat by
    exact matrixEntries_getElem?
      (fun r c => (matrix r c).toNat) row column]
  cases matrix row column <;> rfl

/-- Decode the exact public call atom consumed by `balancedCallProgram`.
The atom is `pair dimension requestCode`, while the request code is the pair
of canonical Boolean-matrix encodings. -/
def rectangularRequestOfAtom (atom : ℕ) : RectangularProductRequest :=
  let dimension := (Nat.unpair atom).1
  let requestCode := (Nat.unpair atom).2
  { dimension := dimension
    left := bitMatrixOfCode dimension (rectangularInnerDimension dimension)
      (Nat.unpair requestCode).1
    right := bitMatrixOfCode (rectangularInnerDimension dimension) dimension
      (Nat.unpair requestCode).2 }

def rectangularCallAtom (request : RectangularProductRequest) : ℕ :=
  Nat.pair request.dimension request.code

def signedEntryBitOutput (atom : ℕ) : ℕ :=
  let input := (Nat.unpair atom).1
  let fields := Nat.unpair (Nat.unpair atom).2
  if ((Nat.unpair input).2 != 0) = (fields.1 != 0) then
    (fields.2.testBit (Nat.unpair input).1).toNat
  else
    0

def signedEntryBitProgram : NPOracleProgram :=
  [ .unpairLeft 1 2 1
  , .unpairRight 1 3 2
  , .unpairLeft 0 4 3
  , .unpairRight 0 5 4
  , .branchZero 3 5 6
  , .branchZero 4 7 8
  , .branchZero 4 8 7
  , .testBit 5 2 0 9
  , .set 0 0 9
  , .halt 0
  ]

@[simp] theorem signedEntryBitProgram_oracleFree :
    ExecutableInterfaces.OracleFree signedEntryBitProgram := by
  rfl

@[simp] theorem signedEntryBitOutput_callAtom
    (bit : ℕ) (negative : Bool) (value : ℤ) :
    signedEntryBitOutput
        (signedPlaneEntryCallAtom bit negative value) =
      (if negative then negativeMagnitudeBit value bit
        else positiveMagnitudeBit value bit).toNat := by
  cases negative
  · cases value with
    | ofNat magnitude =>
        have hnonnegative : (0 : ℤ) ≤ magnitude := Int.natCast_nonneg _
        have hnotNegative : ¬(magnitude : ℤ) < 0 := not_lt.mpr hnonnegative
        simp [signedEntryBitOutput, signedPlaneEntryCallAtom,
          signedPlaneEntryCallInput, signedEntryCode, positiveMagnitudeBit,
          hnonnegative, hnotNegative]
    | negSucc magnitude =>
        have hnegative : Int.negSucc magnitude < 0 :=
          Int.negSucc_lt_zero _
        have hnotNonnegative : ¬(0 : ℤ) ≤ Int.negSucc magnitude :=
          not_le.mpr hnegative
        simp [signedEntryBitOutput, signedPlaneEntryCallAtom,
          signedPlaneEntryCallInput, signedEntryCode, positiveMagnitudeBit,
          hnegative, hnotNonnegative]
  · cases value with
    | ofNat magnitude =>
        have hnonnegative : (0 : ℤ) ≤ magnitude := Int.natCast_nonneg _
        have hnotNegative : ¬(magnitude : ℤ) < 0 := not_lt.mpr hnonnegative
        simp [signedEntryBitOutput, signedPlaneEntryCallAtom,
          signedPlaneEntryCallInput, signedEntryCode,
          negativeMagnitudeBit, hnotNegative]
    | negSucc magnitude =>
        have hnegative : Int.negSucc magnitude < 0 :=
          Int.negSucc_lt_zero _
        have hnotNonnegative : ¬(0 : ℤ) ≤ Int.negSucc magnitude :=
          not_le.mpr hnegative
        simp [signedEntryBitOutput, signedPlaneEntryCallAtom,
          signedPlaneEntryCallInput, signedEntryCode,
          negativeMagnitudeBit, hnegative]

private theorem natBitLength_mono {left right : ℕ} (hle : left ≤ right) :
    natBitLength left ≤ natBitLength right := by
  unfold natBitLength
  exact Nat.add_le_add_right (Nat.log_mono_right hle) 1

private theorem pairLeftBits
    {left right maximumBits : ℕ}
    (hbits : natBitLength (Nat.pair left right) ≤ maximumBits) :
    natBitLength left ≤ maximumBits :=
  (natBitLength_mono (Nat.left_le_pair left right)).trans hbits

private theorem pairRightBits
    {left right maximumBits : ℕ}
    (hbits : natBitLength (Nat.pair left right) ≤ maximumBits) :
    natBitLength right ≤ maximumBits :=
  (natBitLength_mono (Nat.right_le_pair left right)).trans hbits

@[simp] private theorem natCast_not_negative (magnitude : ℕ) :
    ¬(magnitude : ℤ) < 0 :=
  not_lt.mpr (Int.natCast_nonneg magnitude)

set_option maxHeartbeats 2000000 in
-- The exact instruction trace splits on both signs and both integer constructors.
theorem run_signedEntryBitProgram
    (maximumBits bit : ℕ) (negative : Bool) (value : ℤ)
    (hbits :
      natBitLength (signedPlaneEntryCallAtom bit negative value) ≤
        maximumBits) :
    runNPOracleProgram signedEntryBitProgram maximumBits 10
        (initialNPOracleState
          (signedPlaneEntryCallInput bit negative)
          (signedEntryCode value)) =
      some
        ((if negative then negativeMagnitudeBit value bit
          else positiveMagnitudeBit value bit).toNat) := by
  let input := signedPlaneEntryCallInput bit negative
  let code := signedEntryCode value
  have hatom :
      signedPlaneEntryCallAtom bit negative value = Nat.pair input code := rfl
  have hinput : natBitLength input ≤ maximumBits := by
    exact pairLeftBits (hatom ▸ hbits)
  have hcode : natBitLength code ≤ maximumBits := by
    exact pairRightBits (hatom ▸ hbits)
  have hbit : natBitLength bit ≤ maximumBits := by
    exact pairLeftBits hinput
  have hnegative : natBitLength negative.toNat ≤ maximumBits := by
    exact pairRightBits hinput
  have hsign :
      natBitLength (if value < 0 then 1 else 0) ≤ maximumBits := by
    exact pairLeftBits (by simpa [code, signedEntryCode] using hcode)
  have hmagnitude : natBitLength value.natAbs ≤ maximumBits := by
    exact pairRightBits (by simpa [code, signedEntryCode] using hcode)
  have hone : natBitLength 1 ≤ maximumBits := by
    have hpositive : 1 ≤ natBitLength (Nat.pair input code) := by
      simp [natBitLength]
    exact hpositive.trans (hatom ▸ hbits)
  have hzero : natBitLength 0 ≤ maximumBits := by
    simpa [natBitLength] using hone
  have hresult :
      natBitLength
          ((if negative then negativeMagnitudeBit value bit
            else positiveMagnitudeBit value bit).toNat) ≤
        maximumBits := by
    apply (natBitLength_mono ?_).trans hone
    cases negative
    · cases positiveMagnitudeBit value bit <;> simp
    · cases negativeMagnitudeBit value bit <;> simp
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairLeft_instruction (by rfl) rfl
    (by simp [initialNPOracleState, signedPlaneEntryCallInput]) hbit]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      initialNPOracleState, signedPlaneEntryCallInput]) hnegative]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      initialNPOracleState, signedEntryCode]) hsign]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      initialNPOracleState, signedEntryCode]) hmagnitude]
  rw [show 6 = 5 + 1 by omega]
  rw [run_branchZero_instruction (by rfl) rfl]
  cases negative <;> cases value <;>
    simp_all [signedEntryBitProgram, runNPOracleProgram,
      NPOracleState.boundedWrite, initialNPOracleState,
      signedPlaneEntryCallAtom, signedPlaneEntryCallInput,
      signedEntryCode, positiveMagnitudeBit, negativeMagnitudeBit,
      NPOracleState.write, NPOracleState.jump]

theorem signedPlaneEntryBitOutputs
    (request : SignedPlaneBatchRequest) (bit : ℕ) (negative : Bool) :
    (signedPlaneEntryCallAtoms request bit negative).map
        signedEntryBitOutput =
      bitMatrixEntries
        (if negative then negativeBitPlane request.left bit
          else positiveBitPlane request.left bit) := by
  cases negative <;>
    simp [signedPlaneEntryCallAtoms, signedMatrixEntries, signedMatrixRows,
      bitMatrixEntries, positiveBitPlane, negativeBitPlane,
      List.map_flatten, List.map_ofFn, Function.comp_def]

/-! ## One signed bit-plane call -/

/-- Repackage a computed plane code with the dimension and right-matrix code
already carried in the call input. -/
def rectangularAtomPackerOutput (inputLength planeCode : ℕ) : ℕ :=
  let outer := Nat.unpair inputLength
  let payload := Nat.unpair outer.2
  Nat.pair outer.1 (Nat.pair planeCode payload.1)

def rectangularAtomPackerProgram : NPOracleProgram :=
  [ .unpairLeft 1 2 1
  , .unpairRight 1 3 2
  , .unpairLeft 3 4 3
  , .pair 0 4 5 4
  , .pair 2 5 0 5
  , .halt 0
  ]

@[simp] theorem rectangularAtomPackerProgram_oracleFree :
    OracleFree rectangularAtomPackerProgram := by
  rfl

theorem run_rectangularAtomPackerProgram
    (inputLength planeCode maximumBits : ℕ)
    (hinput : natBitLength inputLength ≤ maximumBits)
    (houtput :
      natBitLength (rectangularAtomPackerOutput inputLength planeCode) ≤
        maximumBits) :
    runNPOracleProgram rectangularAtomPackerProgram maximumBits 6
        (initialNPOracleState inputLength planeCode) =
      some (rectangularAtomPackerOutput inputLength planeCode) := by
  let dimension := (Nat.unpair inputLength).1
  let payload := (Nat.unpair inputLength).2
  let rightCode := (Nat.unpair payload).1
  let requestCode := Nat.pair planeCode rightCode
  let output := Nat.pair dimension requestCode
  have hdimension : natBitLength dimension ≤ maximumBits :=
    (natBitLength_mono (Nat.unpair_left_le inputLength)).trans hinput
  have hpayload : natBitLength payload ≤ maximumBits :=
    (natBitLength_mono (Nat.unpair_right_le inputLength)).trans hinput
  have hright : natBitLength rightCode ≤ maximumBits :=
    (natBitLength_mono (Nat.unpair_left_le payload)).trans hpayload
  have houtputEq :
      rectangularAtomPackerOutput inputLength planeCode = output := rfl
  have hrequest : natBitLength requestCode ≤ maximumBits := by
    apply (natBitLength_mono ?_).trans
      (houtputEq ▸ houtput)
    exact Nat.right_le_pair dimension requestCode
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (by rfl) rfl
    (by simp [initialNPOracleState, dimension]) hdimension]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      initialNPOracleState, payload]) hpayload]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, rightCode, payload])
    hright]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      initialNPOracleState, requestCode])
    hrequest]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, initialNPOracleState,
        output, requestCode])
    (houtputEq ▸ houtput)]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by
      simpa [NPOracleState.write, NPOracleState.jump, output] using
        houtputEq.symm)
    (houtputEq ▸ houtput)

def signedPlaneBitEntries (atom : ℕ) : List ℕ :=
  (decodeBalancedList (Nat.unpair atom).2).getD []

def signedPlaneBitCallOutput (atom : ℕ) : ℕ :=
  rectangularAtomPackerOutput (Nat.unpair atom).1
    (encodeBalancedList
      ((signedPlaneBitEntries atom).map signedEntryBitOutput))

def signedPlaneBitCallFuel (atom : ℕ) : ℕ :=
  linkFuel rectangularAtomPackerProgram
    (balancedCallFuel signedEntryBitProgram (fun _ => 10)
      (signedPlaneBitEntries atom))
    6

def signedPlaneBitCallRequiredBits (atom : ℕ) : ℕ :=
  max
    (balancedCallRequiredBits signedEntryBitOutput
      (signedPlaneBitEntries atom))
    (max (natBitLength (Nat.unpair atom).1)
      (natBitLength (signedPlaneBitCallOutput atom)))

def signedPlaneBitProgram : NPOracleProgram :=
  linkPrograms (balancedCallProgram signedEntryBitProgram)
    rectangularAtomPackerProgram

theorem signedPlaneBitProgram_oracleFree :
    OracleFree signedPlaneBitProgram := by
  exact oracleFree_linkPrograms
    (balancedCallProgram_oracleFree signedEntryBitProgram_oracleFree)
    rectangularAtomPackerProgram_oracleFree

@[simp] theorem signedPlaneBitEntries_callAtom
    (request : SignedPlaneBatchRequest) (bit : ℕ) (negative : Bool) :
      signedPlaneBitEntries (signedPlaneBitCallAtom request bit negative) =
      signedPlaneEntryCallAtoms request bit negative := by
  simp [signedPlaneBitEntries, signedPlaneBitCallAtom,
    signedPlaneEntryCallTree]

@[simp] theorem signedPlaneBitCallOutput_asPacker
    (request : SignedPlaneBatchRequest) (bit : ℕ) (negative : Bool) :
    signedPlaneBitCallOutput
        (signedPlaneBitCallAtom request bit negative) =
      rectangularAtomPackerOutput
        (signedPlaneCallInput request bit negative)
        (encodeBalancedList
          ((signedPlaneEntryCallAtoms request bit negative).map
            signedEntryBitOutput)) := by
  unfold signedPlaneBitCallOutput
  rw [signedPlaneBitEntries_callAtom]
  simp [signedPlaneBitCallAtom]

@[simp] theorem signedPlaneBitCallFuel_callAtom
    (request : SignedPlaneBatchRequest) (bit : ℕ) (negative : Bool) :
    signedPlaneBitCallFuel
        (signedPlaneBitCallAtom request bit negative) =
      linkFuel rectangularAtomPackerProgram
        (balancedCallFuel signedEntryBitProgram (fun _ => 10)
          (signedPlaneEntryCallAtoms request bit negative))
        6 := by
  unfold signedPlaneBitCallFuel
  rw [signedPlaneBitEntries_callAtom]

@[simp] theorem signedPlaneBitCallOutput_callAtom
    (request : SignedPlaneBatchRequest) (bit : ℕ) (negative : Bool) :
    signedPlaneBitCallOutput
        (signedPlaneBitCallAtom request bit negative) =
      rectangularCallAtom
        (⟨request.U,
          if negative then negativeBitPlane request.left bit
            else positiveBitPlane request.left bit,
          request.right⟩ : RectangularProductRequest) := by
  unfold signedPlaneBitCallOutput
  rw [show (Nat.unpair
      (signedPlaneBitCallAtom request bit negative)).1 =
        signedPlaneCallInput request bit negative by
      simp [signedPlaneBitCallAtom]]
  rw [signedPlaneBitEntries_callAtom]
  rw [signedPlaneEntryBitOutputs]
  simp [signedPlaneCallInput, rectangularAtomPackerOutput,
    rectangularCallAtom, RectangularProductRequest.code,
    encodeRightMatrix, encodeBitMatrix]

@[simp] theorem signedPlaneBitCallRequiredBits_callAtom
    (request : SignedPlaneBatchRequest) (bit : ℕ) (negative : Bool) :
    signedPlaneBitCallRequiredBits
        (signedPlaneBitCallAtom request bit negative) =
      max
        (balancedCallRequiredBits signedEntryBitOutput
          (signedPlaneEntryCallAtoms request bit negative))
        (max
          (natBitLength (signedPlaneCallInput request bit negative))
          (natBitLength
            (rectangularCallAtom
              (⟨request.U,
                if negative then negativeBitPlane request.left bit
                  else positiveBitPlane request.left bit,
                request.right⟩ : RectangularProductRequest)))) := by
  unfold signedPlaneBitCallRequiredBits
  rw [signedPlaneBitEntries_callAtom,
    signedPlaneBitCallOutput_callAtom]
  simp [signedPlaneBitCallAtom]

theorem run_signedPlaneBitProgram_from
    (inputLength maximumBits : ℕ) (entries : List ℕ)
    (hrequired :
      max (balancedCallRequiredBits signedEntryBitOutput entries)
          (max (natBitLength inputLength)
            (natBitLength
              (rectangularAtomPackerOutput inputLength
                (encodeBalancedList
                  (entries.map signedEntryBitOutput))))) ≤
        maximumBits)
    (hexec :
      ∀ entry, entry ∈ entries →
        runNPOracleProgram signedEntryBitProgram maximumBits 10
            (initialNPOracleState (Nat.unpair entry).1
              (Nat.unpair entry).2) =
          some (signedEntryBitOutput entry)) :
    runNPOracleProgram signedPlaneBitProgram maximumBits
        (linkFuel rectangularAtomPackerProgram
          (balancedCallFuel signedEntryBitProgram (fun _ => 10) entries)
          6)
        (initialNPOracleState inputLength
          (encodeBalancedList entries)) =
      some
        (rectangularAtomPackerOutput inputLength
          (encodeBalancedList (entries.map signedEntryBitOutput))) := by
  have hinner :
      balancedCallRequiredBits signedEntryBitOutput entries ≤
        maximumBits := by
    exact (le_max_left _ _).trans hrequired
  have hinput :
      natBitLength inputLength ≤ maximumBits := by
    exact (le_max_left _ _).trans
      ((le_max_right
        (balancedCallRequiredBits signedEntryBitOutput entries) _).trans
          hrequired)
  have houtput :
      natBitLength
          (rectangularAtomPackerOutput inputLength
            (encodeBalancedList (entries.map signedEntryBitOutput))) ≤
        maximumBits := by
    exact (le_max_right _ _).trans
      ((le_max_right
        (balancedCallRequiredBits signedEntryBitOutput entries) _).trans
          hrequired)
  have hpositive : 1 ≤ maximumBits :=
    (one_le_balancedCallRequiredBits signedEntryBitOutput entries).trans
      hinner
  have hfirst :
      runNPOracleProgram (balancedCallProgram signedEntryBitProgram)
          maximumBits
          (balancedCallFuel signedEntryBitProgram (fun _ => 10) entries)
          (initialNPOracleState
            inputLength
            (encodeBalancedList entries)) =
        some (encodeBalancedList (entries.map signedEntryBitOutput)) := by
    apply run_balancedCallProgram_from
      inputLength entries
        (fun _ => 10) signedEntryBitOutput hinner
    exact hexec
  have hsecond :=
    run_rectangularAtomPackerProgram
      inputLength
      (encodeBalancedList (entries.map signedEntryBitOutput))
      maximumBits hinput houtput
  unfold signedPlaneBitProgram
  apply run_linkPrograms hpositive hinput
  · exact hfirst
  · exact hsecond

set_option maxHeartbeats 1000000 in
-- Resolving every balanced leaf against the dependent matrix entry list is kernel-heavy.
theorem run_signedPlaneBitProgram
    (request : SignedPlaneBatchRequest) (bit : ℕ) (negative : Bool)
    (maximumBits : ℕ)
    (hrequired :
      signedPlaneBitCallRequiredBits
          (signedPlaneBitCallAtom request bit negative) ≤
        maximumBits) :
    runNPOracleProgram signedPlaneBitProgram maximumBits
        (signedPlaneBitCallFuel
          (signedPlaneBitCallAtom request bit negative))
        (initialNPOracleState
          (signedPlaneCallInput request bit negative)
          (signedPlaneEntryCallTree request bit negative)) =
      some
        (signedPlaneBitCallOutput
          (signedPlaneBitCallAtom request bit negative)) := by
  let entries := signedPlaneEntryCallAtoms request bit negative
  have hrequired' :
      max (balancedCallRequiredBits signedEntryBitOutput entries)
          (max
            (natBitLength (signedPlaneCallInput request bit negative))
            (natBitLength
              (rectangularAtomPackerOutput
                (signedPlaneCallInput request bit negative)
                (encodeBalancedList
                  (entries.map signedEntryBitOutput))))) ≤
        maximumBits := by
    unfold signedPlaneBitCallRequiredBits at hrequired
    rw [signedPlaneBitEntries_callAtom] at hrequired
    rw [signedPlaneBitCallOutput_asPacker] at hrequired
    simpa only [signedPlaneBitCallAtom, Nat.unpair_pair] using hrequired
  have hrun :=
    run_signedPlaneBitProgram_from
      (signedPlaneCallInput request bit negative) maximumBits entries
      hrequired' (by
        intro entry hentry
        dsimp [entries] at hentry
        simp only [signedPlaneEntryCallAtoms, List.mem_map] at hentry
        obtain ⟨value, hvalue, rfl⟩ := hentry
        have hentryBits :
            natBitLength (signedPlaneEntryCallAtom bit negative value) ≤
              maximumBits :=
          (balancedCallRequiredBits_request signedEntryBitOutput
            (by
              exact List.mem_map.mpr ⟨value, hvalue, rfl⟩)).trans
            ((le_max_left _ _).trans hrequired')
        rw [signedEntryBitOutput_callAtom]
        simpa [signedPlaneEntryCallAtom, signedPlaneEntryCallInput] using
          run_signedEntryBitProgram maximumBits bit negative value
            hentryBits)
  rw [signedPlaneBitCallFuel_callAtom,
    signedPlaneBitCallOutput_asPacker]
  change
    runNPOracleProgram signedPlaneBitProgram maximumBits
        (linkFuel rectangularAtomPackerProgram
          (balancedCallFuel signedEntryBitProgram (fun _ => 10) entries)
          6)
        (initialNPOracleState
          (signedPlaneCallInput request bit negative)
          (encodeBalancedList entries)) =
      some
        (rectangularAtomPackerOutput
          (signedPlaneCallInput request bit negative)
          (encodeBalancedList (entries.map signedEntryBitOutput)))
  exact hrun

set_option maxHeartbeats 1000000 in
-- The dependent matrix dimensions make this one codec round-trip kernel-heavy.
@[simp] theorem rectangularRequestOfAtom_callAtom
    (request : RectangularProductRequest) :
    rectangularRequestOfAtom (rectangularCallAtom request) = request := by
  cases request with
  | mk dimension left right =>
      unfold rectangularRequestOfAtom rectangularCallAtom
        RectangularProductRequest.code
      dsimp only
      rw [Nat.unpair_pair dimension
        (Nat.pair (encodeBitMatrix left) (encodeBitMatrix right))]
      rw [Nat.unpair_pair (encodeBitMatrix left) (encodeBitMatrix right)]
      rw [bitMatrixOfCode_encodeBitMatrix,
        bitMatrixOfCode_encodeBitMatrix]

def signedPlaneProducts (request : SignedPlaneBatchRequest) :
    List RectangularProductRequest :=
  (List.range request.width).flatMap fun bit =>
    [⟨request.U, positiveBitPlane request.left bit, request.right⟩,
      ⟨request.U, negativeBitPlane request.left bit, request.right⟩]

@[simp] theorem signedPlaneProducts_length
    (request : SignedPlaneBatchRequest) :
    (signedPlaneProducts request).length = 2 * request.width := by
  simp [signedPlaneProducts, List.sum_replicate]
  omega

theorem signedPlaneProducts_dimension
    (request : SignedPlaneBatchRequest)
    (product : RectangularProductRequest)
    (hproduct : product ∈ signedPlaneProducts request) :
    product.dimension = request.U := by
  simp only [signedPlaneProducts, List.mem_flatMap] at hproduct
  obtain ⟨bit, _hbit, hproduct⟩ := hproduct
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hproduct
  rcases hproduct with rfl | rfl <;> rfl

def signedPlaneCallAtoms (request : SignedPlaneBatchRequest) : List ℕ :=
  (signedPlaneProducts request).map rectangularCallAtom

theorem signedPlaneCallAtoms_eq_requestPairs
    (request : SignedPlaneBatchRequest) :
    signedPlaneCallAtoms request =
      (signedPlaneRequests request).map fun call =>
        Nat.pair call.1 call.2 := by
  change
    (signedPlaneProducts request).map
        (fun product => Nat.pair product.dimension product.code) =
      (signedPlaneRequests request).map fun call =>
        Nat.pair call.1 call.2
  simp [signedPlaneProducts, signedPlaneRequests, List.map_flatMap]

@[simp] theorem signedPlaneCallAtoms_length
    (request : SignedPlaneBatchRequest) :
    (signedPlaneCallAtoms request).length = 2 * request.width := by
  simp [signedPlaneCallAtoms]

def rectangularCallOutput
    (algorithm : ExecutableRectangularProductAlgorithm) (atom : ℕ) : ℕ :=
  algorithm.runner.execute (rectangularRequestOfAtom atom)

def rectangularCallFuel
    (algorithm : ExecutableRectangularProductAlgorithm) (atom : ℕ) : ℕ :=
  algorithm.runner.budget (rectangularRequestOfAtom atom)

@[simp] theorem rectangularCallOutput_callAtom
    (algorithm : ExecutableRectangularProductAlgorithm)
    (request : RectangularProductRequest) :
    rectangularCallOutput algorithm (rectangularCallAtom request) =
      algorithm.runner.execute request := by
  simp [rectangularCallOutput]

@[simp] theorem rectangularCallFuel_callAtom
    (algorithm : ExecutableRectangularProductAlgorithm)
    (request : RectangularProductRequest) :
    rectangularCallFuel algorithm (rectangularCallAtom request) =
      algorithm.runner.budget request := by
  simp [rectangularCallFuel]

def signedPlaneBalancedCallBits
    (algorithm : ExecutableRectangularProductAlgorithm)
    (request : SignedPlaneBatchRequest) : ℕ :=
  max
    (balancedCallRequiredBits (rectangularCallOutput algorithm)
      (signedPlaneCallAtoms request))
    (algorithm.runner.budget
      (⟨request.U, positiveBitPlane request.left 0, request.right⟩ :
        RectangularProductRequest))

theorem signedPlaneBalancedCallBits_positive
    (algorithm : ExecutableRectangularProductAlgorithm)
    (request : SignedPlaneBatchRequest) :
    0 < signedPlaneBalancedCallBits algorithm request := by
  unfold signedPlaneBalancedCallBits
  exact lt_of_lt_of_le
    (algorithm.runner.toBounded.registerBitsPositive
      (⟨request.U, positiveBitPlane request.left 0, request.right⟩ :
        RectangularProductRequest))
    (le_max_right _ _)

theorem signedPlaneBalancedCallBits_required
    (algorithm : ExecutableRectangularProductAlgorithm)
    (request : SignedPlaneBatchRequest) :
    balancedCallRequiredBits (rectangularCallOutput algorithm)
        (signedPlaneCallAtoms request) ≤
      signedPlaneBalancedCallBits algorithm request :=
  le_max_left _ _

theorem signedPlaneCallFuel_eq_reference
    (algorithm : ExecutableRectangularProductAlgorithm)
    (request : SignedPlaneBatchRequest)
    (atom : ℕ) (hatom : atom ∈ signedPlaneCallAtoms request) :
    rectangularCallFuel algorithm atom =
      algorithm.runner.budget
        (⟨request.U, positiveBitPlane request.left 0, request.right⟩ :
          RectangularProductRequest) := by
  change atom ∈
    (signedPlaneProducts request).map rectangularCallAtom at hatom
  rw [List.mem_map] at hatom
  obtain ⟨product, hproduct, rfl⟩ := hatom
  rw [rectangularCallFuel_callAtom]
  have hdimension : product.dimension = request.U :=
    signedPlaneProducts_dimension request product hproduct
  simp [PolynomialNatProgram.budget, RectangularProductRequest.measure,
    hdimension]

theorem signedPlaneCallFuel_le_bits
    (algorithm : ExecutableRectangularProductAlgorithm)
    (request : SignedPlaneBatchRequest)
    (atom : ℕ) (hatom : atom ∈ signedPlaneCallAtoms request) :
    rectangularCallFuel algorithm atom ≤
      signedPlaneBalancedCallBits algorithm request := by
  rw [signedPlaneCallFuel_eq_reference algorithm request atom hatom]
  exact le_max_right _ _

theorem signedPlaneBalancedCallFuel_le_uniform
    (algorithm : ExecutableRectangularProductAlgorithm)
    (request : SignedPlaneBatchRequest) :
    balancedCallFuel algorithm.runner.program
        (rectangularCallFuel algorithm) (signedPlaneCallAtoms request) ≤
      35 * (2 * (2 * request.width) + 1) +
        (2 * request.width) *
          balancedCallLeafBudget algorithm.runner.program
            (algorithm.runner.budget
              (⟨request.U, positiveBitPlane request.left 0, request.right⟩ :
                RectangularProductRequest)) + 2 := by
  have hbound :
      ∀ atom, atom ∈ signedPlaneCallAtoms request →
        rectangularCallFuel algorithm atom ≤
          algorithm.runner.budget
            (⟨request.U, positiveBitPlane request.left 0, request.right⟩ :
              RectangularProductRequest) := by
    intro atom hatom
    exact (signedPlaneCallFuel_eq_reference
      algorithm request atom hatom).le
  simpa only [signedPlaneCallAtoms_length] using
    balancedCallFuel_le_uniform algorithm.runner.program
      (rectangularCallFuel algorithm) (signedPlaneCallAtoms request)
      (algorithm.runner.budget
        (⟨request.U, positiveBitPlane request.left 0, request.right⟩ :
          RectangularProductRequest))
      hbound

theorem signedPlaneCallOutputs
    (algorithm : ExecutableRectangularProductAlgorithm)
    (request : SignedPlaneBatchRequest) :
    (signedPlaneCallAtoms request).map (rectangularCallOutput algorithm) =
      (signedPlaneProducts request).map algorithm.runner.execute := by
  unfold signedPlaneCallAtoms
  rw [List.map_map]
  exact List.map_congr_left fun product _hproduct => by
    change rectangularCallOutput algorithm (rectangularCallAtom product) =
      algorithm.runner.execute product
    exact rectangularCallOutput_callAtom algorithm product

set_option maxHeartbeats 1000000 in
-- Elaborating the dependent decoded request against the raw call ABI is local but kernel-heavy.
theorem run_signedPlaneCallAtom
    (algorithm : ExecutableRectangularProductAlgorithm)
    (request : SignedPlaneBatchRequest)
    (atom : ℕ) (hatom : atom ∈ signedPlaneCallAtoms request) :
    runNPOracleProgram algorithm.runner.program
        (signedPlaneBalancedCallBits algorithm request)
        (rectangularCallFuel algorithm atom)
        (initialNPOracleState (Nat.unpair atom).1 (Nat.unpair atom).2) =
      some (rectangularCallOutput algorithm atom) := by
  change atom ∈
    (signedPlaneProducts request).map rectangularCallAtom at hatom
  rw [List.mem_map] at hatom
  obtain ⟨product, hproduct, rfl⟩ := hatom
  rw [rectangularCallFuel_callAtom, rectangularCallOutput_callAtom]
  have hrun := algorithm.runner.run_eq_execute product
  have hbits :=
    signedPlaneCallFuel_le_bits algorithm request
      (rectangularCallAtom product)
      (by
        change rectangularCallAtom product ∈
          (signedPlaneProducts request).map rectangularCallAtom
        exact List.mem_map.mpr ⟨product, hproduct, rfl⟩)
  rw [rectangularCallFuel_callAtom] at hbits
  have hpadded := run_bits_mono hrun hbits
  simpa only [rectangularCallAtom, Nat.unpair_pair,
    RectangularProductRequest.length] using hpadded

theorem run_signedPlaneBalancedCallProgram_from
    (algorithm : ExecutableRectangularProductAlgorithm)
    (inputLength : ℕ) (request : SignedPlaneBatchRequest) :
    runNPOracleProgram
        (balancedCallProgram algorithm.runner.program)
        (signedPlaneBalancedCallBits algorithm request)
        (balancedCallFuel algorithm.runner.program
          (rectangularCallFuel algorithm) (signedPlaneCallAtoms request))
        (initialNPOracleState inputLength
          (encodeBalancedList (signedPlaneCallAtoms request))) =
      some
        (encodeBalancedList
          ((signedPlaneProducts request).map
            algorithm.runner.execute)) := by
  rw [← signedPlaneCallOutputs algorithm request]
  have hrun :=
    run_balancedCallProgram_from inputLength
      (callee := algorithm.runner.program)
      (maximumBits := signedPlaneBalancedCallBits algorithm request)
      (signedPlaneCallAtoms request)
      (rectangularCallFuel algorithm)
      (rectangularCallOutput algorithm)
      (signedPlaneBalancedCallBits_required algorithm request)
      (run_signedPlaneCallAtom algorithm request)
  exact hrun

theorem run_signedPlaneBalancedCallProgram
    (algorithm : ExecutableRectangularProductAlgorithm)
    (request : SignedPlaneBatchRequest) :
    runNPOracleProgram
        (balancedCallProgram algorithm.runner.program)
        (signedPlaneBalancedCallBits algorithm request)
        (balancedCallFuel algorithm.runner.program
          (rectangularCallFuel algorithm) (signedPlaneCallAtoms request))
        (initialNPOracleState (signedPlaneCallAtoms request).length
          (encodeBalancedList (signedPlaneCallAtoms request))) =
      some
        (encodeBalancedList
          ((signedPlaneProducts request).map
            algorithm.runner.execute)) := by
  exact run_signedPlaneBalancedCallProgram_from algorithm
    (signedPlaneCallAtoms request).length request

theorem signedPlaneBalancedCallProgram_oracleFree
    (algorithm : ExecutableRectangularProductAlgorithm) :
    OracleFree (balancedCallProgram algorithm.runner.program) :=
  balancedCallProgram_oracleFree algorithm.oracleFree

/-! ## One raw request to one canonical balanced output -/

@[simp] theorem rectangularAtomPackerOutput_plane
    (request : SignedPlaneBatchRequest) (bit : ℕ) (negative : Bool) :
    rectangularAtomPackerOutput
        (signedPlaneCallInput request bit negative)
        (encodeBalancedList
          ((signedPlaneEntryCallAtoms request bit negative).map
            signedEntryBitOutput)) =
      rectangularCallAtom
        (⟨request.U,
          if negative then negativeBitPlane request.left bit
            else positiveBitPlane request.left bit,
          request.right⟩ : RectangularProductRequest) := by
  rw [← signedPlaneBitCallOutput_asPacker]
  exact signedPlaneBitCallOutput_callAtom request bit negative

theorem signedPlaneRawCallOutputs
    (request : SignedPlaneBatchRequest) :
    (VerifiedPlaneRequestBuilder.signedPlaneCallAtoms request).map
        signedPlaneBitCallOutput =
      signedPlaneCallAtoms request := by
  simp [VerifiedPlaneRequestBuilder.signedPlaneCallAtoms,
    signedPlaneCallAtoms, signedPlaneProducts, List.map_flatMap]

private theorem le_foldr_max_one_of_mem
    {value : ℕ} {values : List ℕ} (hvalue : value ∈ values) :
    value ≤ values.foldr max 1 := by
  induction values with
  | nil => simp at hvalue
  | cons head tail ih =>
      simp only [List.mem_cons] at hvalue
      simp only [List.foldr]
      rcases hvalue with rfl | hvalue
      · exact le_max_left _ _
      · exact (ih hvalue).trans (le_max_right _ _)

def signedPlaneRequestTreeProgram : NPOracleProgram :=
  balancedCallProgram signedPlaneBitProgram

def signedPlaneRequestTreeBits
    (request : SignedPlaneBatchRequest) : ℕ :=
  let calls := VerifiedPlaneRequestBuilder.signedPlaneCallAtoms request
  max (natBitLength request.U)
    (max
      (balancedCallRequiredBits signedPlaneBitCallOutput calls)
      ((calls.map signedPlaneBitCallRequiredBits).foldr max 1))

def signedPlaneRequestTreeFuel
    (request : SignedPlaneBatchRequest) : ℕ :=
  balancedCallFuel signedPlaneBitProgram signedPlaneBitCallFuel
    (VerifiedPlaneRequestBuilder.signedPlaneCallAtoms request)

theorem requestDimensionBits_le_requestTreeBits
    (request : SignedPlaneBatchRequest) :
    natBitLength request.U ≤ signedPlaneRequestTreeBits request := by
  exact le_max_left _ _

theorem signedPlaneRequestTreeBits_positive
    (request : SignedPlaneBatchRequest) :
    0 < signedPlaneRequestTreeBits request := by
  have : 0 < natBitLength request.U := by
    unfold natBitLength
    omega
  exact this.trans_le (requestDimensionBits_le_requestTreeBits request)

theorem signedPlaneRequestCodeBits_le_requestTreeBits
    (request : SignedPlaneBatchRequest) :
    natBitLength (encodeSignedPlaneBatchRequest request) ≤
      signedPlaneRequestTreeBits request := by
  let calls := VerifiedPlaneRequestBuilder.signedPlaneCallAtoms request
  have hcode :
      natBitLength (encodeBalancedList calls) ≤
        balancedCallRequiredBits signedPlaneBitCallOutput calls := by
    apply le_trans _ <|
      balancedCallRequiredBits_traversal signedPlaneBitCallOutput calls
    unfold balancedTraversalRequiredBits
    rw [balancedTraversalTree_code]
    exact le_max_left _ _
  exact hcode.trans <|
    (le_max_left _ _).trans (le_max_right _ _)

theorem signedPlaneRequestInitialBitsFit
    (request : SignedPlaneBatchRequest) :
    natBitLength
        (max request.U (encodeSignedPlaneBatchRequest request)) ≤
      signedPlaneRequestTreeBits request := by
  by_cases horder :
      request.U ≤ encodeSignedPlaneBatchRequest request
  · rw [max_eq_right horder]
    exact signedPlaneRequestCodeBits_le_requestTreeBits request
  · rw [max_eq_left (Nat.le_of_not_ge horder)]
    exact requestDimensionBits_le_requestTreeBits request

theorem run_signedPlaneRequestTreeProgram
    (request : SignedPlaneBatchRequest) :
    runNPOracleProgram signedPlaneRequestTreeProgram
        (signedPlaneRequestTreeBits request)
        (signedPlaneRequestTreeFuel request)
        (initialNPOracleState request.U
          (encodeSignedPlaneBatchRequest request)) =
      some (encodeBalancedList (signedPlaneCallAtoms request)) := by
  let calls := VerifiedPlaneRequestBuilder.signedPlaneCallAtoms request
  have houter :
      balancedCallRequiredBits signedPlaneBitCallOutput calls ≤
        signedPlaneRequestTreeBits request := by
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hrun :=
    run_balancedCallProgram_from request.U calls
      signedPlaneBitCallFuel signedPlaneBitCallOutput houter (by
        intro atom hatom
        have hinner :
            signedPlaneBitCallRequiredBits atom ≤
              signedPlaneRequestTreeBits request := by
          have hmem :
              signedPlaneBitCallRequiredBits atom ∈
                calls.map signedPlaneBitCallRequiredBits :=
            List.mem_map.mpr ⟨atom, hatom, rfl⟩
          exact
            (le_foldr_max_one_of_mem hmem).trans <|
              (le_max_right _ _).trans (le_max_right _ _)
        dsimp [calls] at hatom
        simp only [VerifiedPlaneRequestBuilder.signedPlaneCallAtoms,
          List.mem_flatMap] at hatom
        obtain ⟨bit, hbit, hatom⟩ := hatom
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hatom
        rcases hatom with rfl | rfl
        · simpa [signedPlaneBitCallAtom] using
            run_signedPlaneBitProgram request bit false
              (signedPlaneRequestTreeBits request) hinner
        · simpa [signedPlaneBitCallAtom] using
            run_signedPlaneBitProgram request bit true
              (signedPlaneRequestTreeBits request) hinner)
  unfold signedPlaneRequestTreeProgram signedPlaneRequestTreeFuel
  rw [signedPlaneRawCallOutputs] at hrun
  exact hrun

theorem signedPlaneRequestTreeProgram_oracleFree :
    OracleFree signedPlaneRequestTreeProgram :=
  balancedCallProgram_oracleFree signedPlaneBitProgram_oracleFree

/-- The production signed-plane program has one public raw query and one
canonical balanced-list result.  Both linking seams are literal machine
executions; no semantic callback or legacy accumulator remains in the path. -/
def signedPlanePrinterProgram
    (algorithm : ExecutableRectangularProductAlgorithm) : NPOracleProgram :=
  linkPrograms signedPlaneRequestTreeProgram
    (balancedCallProgram algorithm.runner.program)

def signedPlanePrinterBits
    (algorithm : ExecutableRectangularProductAlgorithm)
    (request : SignedPlaneBatchRequest) : ℕ :=
  max (signedPlaneRequestTreeBits request)
    (signedPlaneBalancedCallBits algorithm request)

def signedPlanePrinterFuel
    (algorithm : ExecutableRectangularProductAlgorithm)
    (request : SignedPlaneBatchRequest) : ℕ :=
  linkFuel (balancedCallProgram algorithm.runner.program)
    (signedPlaneRequestTreeFuel request)
    (balancedCallFuel algorithm.runner.program
      (rectangularCallFuel algorithm) (signedPlaneCallAtoms request))

theorem signedPlanePrinterFuel_exact
    (algorithm : ExecutableRectangularProductAlgorithm)
    (request : SignedPlaneBatchRequest) :
    signedPlanePrinterFuel algorithm request =
      signedPlaneRequestTreeFuel request +
        balancedCallFuel algorithm.runner.program
          (rectangularCallFuel algorithm) (signedPlaneCallAtoms request) +
        programRegisterSpan
          (balancedCallProgram algorithm.runner.program) + 5 := by
  exact linkFuel_exact (balancedCallProgram algorithm.runner.program)
    (signedPlaneRequestTreeFuel request)
    (balancedCallFuel algorithm.runner.program
      (rectangularCallFuel algorithm) (signedPlaneCallAtoms request))

theorem requestTreeBits_le_printerBits
    (algorithm : ExecutableRectangularProductAlgorithm)
    (request : SignedPlaneBatchRequest) :
    signedPlaneRequestTreeBits request ≤
      signedPlanePrinterBits algorithm request :=
  le_max_left _ _

theorem balancedCallBits_le_printerBits
    (algorithm : ExecutableRectangularProductAlgorithm)
    (request : SignedPlaneBatchRequest) :
    signedPlaneBalancedCallBits algorithm request ≤
      signedPlanePrinterBits algorithm request :=
  le_max_right _ _

theorem signedPlanePrinterBits_positive
    (algorithm : ExecutableRectangularProductAlgorithm)
    (request : SignedPlaneBatchRequest) :
    0 < signedPlanePrinterBits algorithm request :=
  (signedPlaneRequestTreeBits_positive request).trans_le
    (requestTreeBits_le_printerBits algorithm request)

theorem run_signedPlanePrinterProgram
    (algorithm : ExecutableRectangularProductAlgorithm)
    (request : SignedPlaneBatchRequest) :
    runNPOracleProgram (signedPlanePrinterProgram algorithm)
        (signedPlanePrinterBits algorithm request)
        (signedPlanePrinterFuel algorithm request)
        (initialNPOracleState request.U
          (encodeSignedPlaneBatchRequest request)) =
      some
        (encodeBalancedList
          ((signedPlaneProducts request).map
            algorithm.runner.execute)) := by
  unfold signedPlanePrinterProgram signedPlanePrinterFuel
  apply run_linkPrograms
  · exact signedPlanePrinterBits_positive algorithm request
  · exact (requestDimensionBits_le_requestTreeBits request).trans
      (requestTreeBits_le_printerBits algorithm request)
  · exact run_bits_mono
      (run_signedPlaneRequestTreeProgram request)
      (requestTreeBits_le_printerBits algorithm request)
  · exact run_bits_mono
      (run_signedPlaneBalancedCallProgram_from algorithm request.U request)
      (balancedCallBits_le_printerBits algorithm request)

theorem signedPlanePrinterProgram_oracleFree
    (algorithm : ExecutableRectangularProductAlgorithm) :
    OracleFree (signedPlanePrinterProgram algorithm) := by
  exact oracleFree_linkPrograms signedPlaneRequestTreeProgram_oracleFree
    (signedPlaneBalancedCallProgram_oracleFree algorithm)

def signedPlanePrinterRunner
    (algorithm : ExecutableRectangularProductAlgorithm) :
    BoundedNatProgram SignedPlaneBatchRequest
      (fun request => request.U) encodeSignedPlaneBatchRequest where
  program := signedPlanePrinterProgram algorithm
  fuel := signedPlanePrinterFuel algorithm
  registerBits := signedPlanePrinterBits algorithm
  fuelPositive := by
    intro request
    simp [signedPlanePrinterFuel, linkFuel]
  registerBitsPositive := signedPlanePrinterBits_positive algorithm
  initialBitsFit := by
    intro request
    exact (signedPlaneRequestInitialBitsFit request).trans
      (requestTreeBits_le_printerBits algorithm request)

def signedPlaneExactBatchPrinterCertificate
    (algorithm : ExecutableRectangularProductAlgorithm) :
    ExactBatchPrinterCertificate SignedPlaneBatchRequest where
  queryLength := fun request => request.U
  encodeQuery := encodeSignedPlaneBatchRequest
  targetCode := fun request =>
    encodeBalancedList
      ((signedPlaneProducts request).map algorithm.runner.execute)
  runner := signedPlanePrinterRunner algorithm
  oracleFree := signedPlanePrinterProgram_oracleFree algorithm
  computes := run_signedPlanePrinterProgram algorithm
  stepBound := signedPlanePrinterFuel algorithm
  withinBound := fun _ => le_rfl

/-- The unique semantic view of a balanced signed-plane output batch.  The
raw output order remains positive/negative for each bit from low to high. -/
def decodeSignedPlaneBalancedOutputs
    (request : SignedPlaneBatchRequest) (code : ℕ) :
    List (NatMatrix request.U request.U) :=
  ((decodeBalancedList code).getD []).map
    (decodeNatMatrix request.U request.U)

@[simp] theorem decodeSignedPlaneBalancedOutputs_encode
    (request : SignedPlaneBatchRequest) (outputs : List ℕ) :
    decodeSignedPlaneBalancedOutputs request (encodeBalancedList outputs) =
      outputs.map (decodeNatMatrix request.U request.U) := by
  simp [decodeSignedPlaneBalancedOutputs]

theorem decodeSignedPlaneBalancedOutputs_callResult
    (algorithm : ExecutableRectangularProductAlgorithm)
    (request : SignedPlaneBatchRequest) :
    decodeSignedPlaneBalancedOutputs request
        (encodeBalancedList
          ((signedPlaneProducts request).map algorithm.runner.execute)) =
      (signedPlaneProducts request).map fun product =>
        decodeNatMatrix request.U request.U
          (algorithm.runner.execute product) := by
  simp [decodeSignedPlaneBalancedOutputs]

end NearCubicWires.CanonicalSignedPlaneCall
