import Proof.MachineModel.OrdinaryMatrixRightPaperEntry
import Proof.MachineModel.OrdinaryMatrixScorePhi

/-! Literal raw cut input for the ordinary B.3 producer. Scalar frames are
part of the logical word; the external source is one outer `frame word`.
No scores, matrices, unary templates or sorted records are input data. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreBatch
open LocalBitMultitape SupplierPrinter SignedSortKey RepairRepresentation ExecutableInterfaces SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Cut where
  leftWeights : List ℤ
  rightWeights : List ℤ
  threshold : ℤ
  coefficient : ℤ

structure Request where
  d : ℕ
  p : ℕ
  cuts : List Cut
  /-- The weight count `d'` (number of center bits). -/
  width : ℕ := d
  /-- The columns of the row transform `φ`. -/
  column : ℕ → ℕ := fun j => 2^j

  widthLe : width ≤ 2*d := by omega
  /-- Each column of `φ` is a `width`-bit word. -/
  columnFits : ∀ j,j<d → column j<2^width := by intro j hj; exact Nat.pow_lt_pow_right (by decide) hj
  lengths : ∀ c ∈ cuts,c.leftWeights.length=width ∧ c.rightWeights.length=width
  fits : ∀ c ∈ cuts,
    (∀ w ∈ c.leftWeights++c.rightWeights,w.natAbs<2^p) ∧
    c.threshold.natAbs<2^p ∧ c.coefficient.natAbs<2^p
  gateSquare : cuts.length*cuts.length ≤ rectangularInnerDimension (2^d)

def Request.U (r : Request) : ℕ := 2^r.d
def Request.Gates (r : Request) : ℕ := r.cuts.length
/-- Score width. Variant B: unchanged from Theorem 2.5; `width ≤ 2d` keeps every score below `2^S`
(`score_bound`). -/
def Request.S (r : Request) : ℕ := r.p+natBitLength r.d+2
/-- One common coordinate width permits the paid right-coordinate swap. -/
def Request.M (r : Request) : ℕ := natBitLength (r.U+r.U)+1
def Request.Capacity (r : Request) : ℕ := rectangularInnerDimension r.U
def Request.bucketSize (r : Request) : ℕ :=
  stableCapacityBucketSize r.U r.U r.Capacity r.Gates
def Request.Buckets (r : Request) : ℕ := stableDominanceBucketCount r.U r.U r.bucketSize
def Request.Used (r : Request) : ℕ := r.Gates*r.Buckets

def signMagnitude (p : ℕ) (z : ℤ) : List Bool := decide (z<0)::binary p z.natAbs
def decodeSignMagnitude : List Bool → ℤ
  | [] => 0
  | sign::bits => if sign then -(RadixSemantics.value bits : ℤ) else (RadixSemantics.value bits : ℤ)
def fields (c : Cut) : List ℤ := c.leftWeights++c.rightWeights++[c.threshold,c.coefficient]
def cutWord (p : ℕ) (c : Cut) : List Bool := (fields c).flatMap (fun z => frame (signMagnitude p z))
/-- The columns of `φ`, one per row bit. -/
def Request.cols (r : Request) : List ℕ := (List.range r.d).map r.column
/-- The raw header: row width, coefficient width, gate count, then the weight count and the
columns of `φ` (each a framed `width`-bit word). -/
def header (r : Request) : List Bool :=
  natWord r.d++natWord r.p++natWord r.Gates++natWord r.width++MatrixScorePhi.columnsWord r.width r.cols
def word (r : Request) : List Bool := header r++r.cuts.flatMap (cutWord r.p)
def physicalInput (r : Request) : List Bool := frame (word r)

/-- Assignment indices are in the same least-significant-bit order as `binary`. -/
def linearForm (weights : List ℤ) (assignment : ℕ) : ℤ :=
  (weights.zipIdx.map (fun wi => if assignment.testBit wi.2 then wi.1 else 0)).sum
/-- `φ(n)`: the center bits of row/column `n` (the exclusive-or of the columns selected by the
bits `j < d` of `n`), as the printer's assignment. -/
def Request.phi (r : Request) (n : ℕ) : ℕ := MatrixScorePhi.value r.cols n
def leftScore (r : Request) : IntMatrix r.U r.Gates := fun row gate =>
  (r.cuts.get gate).threshold-linearForm (r.cuts.get gate).leftWeights (r.phi row.val)
def rightScore (r : Request) : IntMatrix r.Gates r.U := fun gate column =>
  linearForm (r.cuts.get gate).rightWeights (r.phi column.val)
def weight (r : Request) (gate : Fin r.Gates) : ℤ := (r.cuts.get gate).coefficient

theorem signMagnitude_decode (p : ℕ) (z : ℤ) (hz : z.natAbs<2^p) :
    decodeSignMagnitude (signMagnitude p z)=z := by
  simp only [decodeSignMagnitude,signMagnitude,binary_value p z.natAbs hz]
  by_cases h : z<0
  · simp [h,abs_of_neg h]
  · simp [h,abs_of_nonneg (by omega : 0≤z)]

@[simp] theorem signMagnitude_length (p : ℕ) (z : ℤ) : (signMagnitude p z).length=p+1 := by
  simp [signMagnitude]

theorem cutWord_length (r : Request) (c : Cut) (hc : c ∈ r.cuts) :
    (cutWord r.p c).length=(2*r.width+2)*(2*r.p+3) := by
  obtain ⟨hl,hr⟩ := r.lengths c hc
  simp [cutWord,fields,List.length_flatMap,hl,hr]
  ring

theorem word_length (r : Request) :
    (word r).length=(header r).length+r.Gates*((2*r.width+2)*(2*r.p+3)) := by
  have hm : r.cuts.map (fun c => (cutWord r.p c).length)=
      r.cuts.map (fun _ => (2*r.width+2)*(2*r.p+3)) := by
    apply List.map_congr_left
    intro c hc
    exact cutWord_length r c hc
  simp only [word,List.length_append,List.length_flatMap]
  rw [hm]
  simp [Request.Gates]

theorem capacity (r : Request) : r.Used≤r.Capacity :=
  stableCapacityBucketDimension_le r.U r.U r.Capacity r.Gates r.gateSquare

theorem dimension_positive (r : Request) : 0<r.U := by
  exact Nat.pow_pos (by decide)

/-- The score width grows by at most one bit over the row width (`width ≤ 2d`). -/
theorem natBitLength_width_le (r : Request) : natBitLength r.width≤natBitLength r.d+1 := by
  have hd : r.d<2^natBitLength r.d := Nat.lt_pow_succ_log_self (by decide) r.d
  have hw : r.width<2^(natBitLength r.d+1) := by have := r.widthLe; rw [Nat.pow_succ]; omega
  unfold natBitLength at hw ⊢
  by_cases h0 : r.width=0
  · rw [h0]; simp
  · have := Nat.log_lt_of_lt_pow h0 hw
    omega

theorem natBitLength_width_le_succ (r : Request) : natBitLength r.width≤r.d+1 := by
  have hw : r.width<2^(r.d+1) := by
    have h1 := r.widthLe
    have h2 : r.d<2^r.d := Nat.lt_two_pow_self
    rw [Nat.pow_succ]; omega
  unfold natBitLength
  by_cases h0 : r.width=0
  · rw [h0]; simp
  · have := Nat.log_lt_of_lt_pow h0 hw; omega

theorem S_le (r : Request) : r.S≤r.p+natBitLength r.d+3 := by
  unfold Request.S; omega

theorem S_le_linear (r : Request) : r.S≤r.p+r.d+3 := by
  have h1 := natBitLength_width_le_succ r
  have h2 : natBitLength r.d≤r.d+1 := Nat.add_le_add_right (Nat.log_le_self _ _) _
  unfold Request.S; omega

/-- Theorem 2.5's instance: with the identity columns, `φ(n) = n` on the `2^d` rows. -/
theorem phi_of_identity (r : Request) (h : r.column=fun j => 2^j) (n : ℕ) (hn : n<r.U) : r.phi n=n := by
  unfold Request.phi Request.cols
  rw [h]
  exact MatrixScorePhi.value_identity r.d n hn

theorem cols_length (r : Request) : r.cols.length=r.d := by simp [Request.cols]

theorem cols_fit (r : Request) : ∀ x ∈ r.cols,x<2^r.width := by
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
  exact r.columnFits j (List.mem_range.mp hj)

theorem phi_lt (r : Request) (n : ℕ) : r.phi n<2^r.width :=
  MatrixScorePhi.value_lt r.cols n r.width (cols_fit r)

/-- `value` reads only the bits `j < cols.length` of its argument. -/
theorem value_congr (cols : List ℕ) (n n' : ℕ) (h : ∀ j,j<cols.length → n.testBit j=n'.testBit j) :
    MatrixScorePhi.value cols n=MatrixScorePhi.value cols n' := by
  unfold MatrixScorePhi.value
  apply List.foldl_ext
  intro acc cj hcj
  have hj : cj.2<cols.length := by
    have := List.mem_zipIdx hcj
    omega
  rw [h cj.2 hj]

/-- `φ(0) = 0`: the first record of each half starts from the zero assignment. -/
theorem phi_zero (r : Request) : r.phi 0=0 := by
  unfold Request.phi MatrixScorePhi.value
  generalize r.cols.zipIdx=l
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.foldl_cons,Nat.zero_testBit]

/-- The right copies have ids `U + n`; `φ` reads only the low `d` bits, so they see `φ(n)`. -/
theorem phi_right (r : Request) (n : ℕ) : r.phi (r.U+n)=r.phi n := by
  unfold Request.phi
  apply value_congr
  intro j hj
  rw [cols_length] at hj
  exact Nat.testBit_two_pow_add_gt hj n

end NearCubicWires.RepairOrdinary.MatrixScoreBatch
