import Proof.Wire_3_5.PrimAsmWriterIface
import Proof.Wire_3_5.CompilerMachineReqContract3

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Geo
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.SupplierPipeline NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine

variable (P : StarParams)

/-! ## The halves and the code basis -/

def hL : ℕ := (P.n - P.r * P.b + 1) / 2

def dB : ℕ := P.b - P.s

def side : List Bool := List.ofFn P.centerSide

/-- The dense width: the left half's coordinates, `r/2` blocks and `⌈(n−rb)/2⌉` unblocked ones. -/
def width : ℕ := P.r / 2 * P.b + hL P

def dRow : ℕ := P.leftCenterBits

/-- The parity positions of the block code: `i + 1` a power of two below `2^s`. -/
def isPar (i : ℕ) : Bool := (List.range P.s).any fun t => i + 1 == 2 ^ t

/-- The data positions of the block code, increasing. -/
def dataPos : List ℕ := (List.range P.b).filter fun i => !isPar P i

/-- The `m`-th data position. -/
def dpos (m : ℕ) : ℕ := (dataPos P).getD m 0

def cwBit (i q : ℕ) : Bool := q == i || (List.range P.s).any fun t => (i + 1).testBit t && q + 1 == 2 ^ t

/-- **Column `j` of `φ`**, bit `p` of the half: for `j < (r/2)(b−s)` the basis vector of data position `j mod (b−s)`
in block `j / (b−s)`; otherwise the unit vector of the unblocked coordinate `j − (r/2)(b−s)`. -/
def colBit (j p : ℕ) : Bool :=
  if j < P.r / 2 * dB P then
    decide (p < P.r / 2 * P.b) && (p / P.b == j / dB P) && cwBit P (dpos P (j % dB P)) (p % P.b)
  else p == P.r / 2 * P.b + (j - P.r / 2 * dB P)

/-- Column `j` as a `width`-bit word. -/
def colBits (j : ℕ) : List Bool := List.ofFn fun p : Fin (width P) => colBit P j p

/-- **The columns of `φ`** (`MatrixScorePhi.value cols`: a row's bits select columns, XORed). -/
def cols : List ℕ := (List.range (dRow P)).map fun j => CanonicalBinary.bitsValue (colBits P j)

/-- The table's multiplicity: `2` when `n − rb` is odd (the right half has one bit fewer; its top row bit is
ignored), else `1`. -/
def mult : ℕ := if (P.n - P.r * P.b) % 2 = 1 then 2 else 1

/-! ## The coset offset, the corners, the flips -/

variable (σ : P.Translation)

/-- Block `j` of the offset: the unit vector whose column is `σ_j` (`0` when `σ_j = 0`), a point of the coset. -/
def offBlock (j : Fin P.r) : Fin P.b → Bool := P.errBits (P.errorOf (σ j) fun _ => false)

/-- **The offset**: a point of the coset `σ` in every block, `0` on the unblocked coordinates. -/
def offset : BitInput P.n :=
  fun x => decide (∃ j : Fin P.r, ∃ i : Fin P.b, P.blockCoord j i = x ∧ offBlock P σ j i = true)

def cornerPt {n : ℕ} (c u v : BitInput n) : Fin 4 → BitInput n :=
  ![xorInput (xorInput c u) v, xorInput c u, xorInput c v, c]

theorem corners_eq {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) (k : Fin 4) :
    Stars.corners T c u v k = T (cornerPt c u v k) := by
  fin_cases k <;> rfl

/-- The block errors of a cell coordinate (`callEqv`'s inverse, the index read modulo `2^{kh}`). -/
def errAt (e : ℕ) : P.Errors :=
  (SeedFix.callEqv P).symm ⟨e % 2 ^ SeedFix.callKh P, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- **The flip pattern of corner `k` of cell `cn`** (`cn = cellNumC x = x.2 + N·x.1`): the corner point of the
offset at the cell's left and right errors. -/
def flipAt (cn k : ℕ) : BitInput P.n :=
  cornerPt (offset P σ) (P.errorVector P.leftBlock (errAt P (cn / 2 ^ SeedFix.callKh P)))
    (P.errorVector P.rightBlock (errAt P (cn % 2 ^ SeedFix.callKh P))) ⟨k % 4, Nat.mod_lt _ (by norm_num)⟩

/-- **The flip patterns** of the call's pool, at indices `4·cn + k` for the `N²` cells and the four corners. -/
def flips : List (List Bool) :=
  List.ofFn fun idx : Fin (4 * (2 ^ SeedFix.callKh P * 2 ^ SeedFix.callKh P)) =>
    List.ofFn (flipAt P σ (idx.val / 4) (idx.val % 4))

/-- **The center at table position `(row, col)`**: the pulled-back point of the offset at `(φ row, φ col)`. -/
def centerAt (row col : ℕ) : BitInput P.n :=
  Pool.pullPoint (side P) (List.ofFn (offset P σ)) (MatrixScorePhi.value (cols P) row)
    (MatrixScorePhi.value (cols P) col)

/-! ## The pool request and the compiler's fields -/

/-- A normalized gate with the full support (the native word reads only the gate). -/
def suppG {n : ℕ} (g : NormalizedThresholdGate n) : SupportedNormalizedGate n :=
  ⟨g, Finset.univ, fun i hi => absurd (Finset.mem_univ i) hi⟩

/-- **The call's pool request** (C3a's `PoolReq`): the pool gates, the halves, the width, the flips, the field width
`h`, the lift precision `Q'` and the load. -/
def poolReq (gates : List (NormalizedThresholdGate P.n)) (h Q psi : ℕ) : Pool.PoolReq :=
  ⟨P.n, gates.map suppG, side P, width P, flips P σ, h, Q, psi⟩

/-- C3a's side field. -/
def sideField : List Bool := frame (side P)

/-- C3a's flips field (a stream of frames). -/
def flipsField : List Bool := Kit.streamTape (flips P σ) []

/-- C3's column header field: `frame (natWord width ++ columnsWord width cols)`. -/
def colsField : List Bool := frame (natWord (width P) ++ MatrixScorePhi.columnsWord (width P) (cols P))

/-- C3a's gate field: the pool gates' native stream, with the arity `1^n` as the opaque top payload. -/
def gateField {n : ℕ} (gates : List (NormalizedThresholdGate n)) : List Bool :=
  frame (ExtDecompositionBatch.segment (gates.map suppG) (List.replicate n true))

end NearCubicWires.WireExponent3_5.PrimT.C4Geo
