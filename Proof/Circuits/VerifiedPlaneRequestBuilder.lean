import Proof.Foundations.CanonicalBinary
import Proof.Foundations.ExecutableInterfaces
import Proof.Foundations.SupplierPrinter

/-!
# Canonical signed-plane request syntax

Signed-plane batches are machine input, so every variable-length component is
midpoint-balanced.  The old implementation first materialized linked token
streams and then bounded them by repeated self-pairing; both choices made the
claimed register envelope exponential in the number of entries.  The sole
production syntax below instead expands the deterministic bit/sign schedule
into balanced call atoms.  It duplicates only source data and public indices,
never a bit plane, product, score, or semantic answer.
-/

namespace NearCubicWires.VerifiedPlaneRequestBuilder

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPrinter

structure SignedPlaneBatchRequest where
  U : ℕ
  width : ℕ
  left : IntMatrix U (rectangularInnerDimension U)
  right : BitMatrix (rectangularInnerDimension U) U

/-! ## Width-safe row-major source data -/

def signedMatrixRows (request : SignedPlaneBatchRequest) : List (List ℤ) :=
  List.ofFn fun row =>
    List.ofFn fun column => request.left row column

def bitMatrixRows (request : SignedPlaneBatchRequest) : List (List Bool) :=
  List.ofFn fun row =>
    List.ofFn fun column => request.right row column

def signedMatrixEntries (request : SignedPlaneBatchRequest) : List ℤ :=
  (signedMatrixRows request).flatten

def signedEntryCode (value : ℤ) : ℕ :=
  Nat.pair (if value < 0 then 1 else 0) value.natAbs

def decodeSignedEntryCode (code : ℕ) : ℤ :=
  let fields := Nat.unpair code
  if fields.1 = 0 then (fields.2 : ℤ) else -(fields.2 : ℤ)

@[simp] theorem decodeSignedEntryCode_signedEntryCode (value : ℤ) :
    decodeSignedEntryCode (signedEntryCode value) = value := by
  cases value with
  | ofNat magnitude =>
      simp [decodeSignedEntryCode, signedEntryCode]
  | negSucc magnitude =>
      simp [decodeSignedEntryCode, signedEntryCode]
      omega

def encodeSignedMatrix (request : SignedPlaneBatchRequest) : ℕ :=
  encodeBalancedList ((signedMatrixEntries request).map signedEntryCode)

def encodeRightMatrix (request : SignedPlaneBatchRequest) : ℕ :=
  encodeBitMatrix request.right

@[simp] theorem signedMatrixEntries_length
  (request : SignedPlaneBatchRequest) :
    (signedMatrixEntries request).length =
      request.U * rectangularInnerDimension request.U := by
  simp [signedMatrixEntries, signedMatrixRows, List.length_flatten,
    List.sum_ofFn]

def signedPlaneEntryCallInput (bit : ℕ) (negative : Bool) : ℕ :=
  Nat.pair bit negative.toNat

def signedPlaneEntryCallAtom (bit : ℕ) (negative : Bool)
    (value : ℤ) : ℕ :=
  Nat.pair (signedPlaneEntryCallInput bit negative) (signedEntryCode value)

def signedPlaneEntryCallAtoms (request : SignedPlaneBatchRequest)
    (bit : ℕ) (negative : Bool) : List ℕ :=
  (signedMatrixEntries request).map
    (signedPlaneEntryCallAtom bit negative)

def signedPlaneEntryCallTree (request : SignedPlaneBatchRequest)
    (bit : ℕ) (negative : Bool) : ℕ :=
  encodeBalancedList (signedPlaneEntryCallAtoms request bit negative)

def signedPlaneCallInput (request : SignedPlaneBatchRequest)
    (bit : ℕ) (negative : Bool) : ℕ :=
  Nat.pair request.U
    (Nat.pair (encodeRightMatrix request)
      (Nat.pair bit negative.toNat))

def signedPlaneBitCallAtom (request : SignedPlaneBatchRequest)
    (bit : ℕ) (negative : Bool) : ℕ :=
  Nat.pair (signedPlaneCallInput request bit negative)
    (signedPlaneEntryCallTree request bit negative)

def signedPlaneCallAtoms (request : SignedPlaneBatchRequest) : List ℕ :=
  (List.range request.width).flatMap fun bit =>
    [signedPlaneBitCallAtom request bit false,
      signedPlaneBitCallAtom request bit true]

/-- The public request is already the unique balanced call tree consumed by
the production batch program; no linked-list conversion stage remains. -/
def encodeSignedPlaneBatchRequest
    (request : SignedPlaneBatchRequest) : ℕ :=
  encodeBalancedList (signedPlaneCallAtoms request)

@[simp] theorem signedPlaneEntryCallAtoms_length
    (request : SignedPlaneBatchRequest) (bit : ℕ) (negative : Bool) :
    (signedPlaneEntryCallAtoms request bit negative).length =
      request.U * rectangularInnerDimension request.U := by
  simp [signedPlaneEntryCallAtoms]

@[simp] theorem signedPlaneCallAtoms_length
    (request : SignedPlaneBatchRequest) :
    (signedPlaneCallAtoms request).length = 2 * request.width := by
  simp [signedPlaneCallAtoms, List.sum_replicate]
  omega

/-! ## Semantic rectangular requests, in exactly the executable order -/

def signedPlaneRequests (request : SignedPlaneBatchRequest) :
    List (ℕ × ℕ) :=
  (List.range request.width).flatMap fun bit =>
    let positive : RectangularProductRequest :=
      ⟨request.U, positiveBitPlane request.left bit, request.right⟩
    let negative : RectangularProductRequest :=
      ⟨request.U, negativeBitPlane request.left bit, request.right⟩
    [(request.U, positive.code), (request.U, negative.code)]

@[simp] theorem signedPlaneRequests_length
    (request : SignedPlaneBatchRequest) :
    (signedPlaneRequests request).length = 2 * request.width := by
  simp [signedPlaneRequests, List.sum_replicate]
  omega

end NearCubicWires.VerifiedPlaneRequestBuilder
