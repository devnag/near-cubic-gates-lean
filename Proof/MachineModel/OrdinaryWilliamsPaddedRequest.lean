import Proof.Foundations.RepresentationSourceContracts

/-! Exact positive-power request used by the actual padding/cropping
wrapper. These equations justify its physical zero padding and crop. -/
namespace NearCubicWires.RepairOrdinary.WilliamsPaddedRequest
open SourceInterfaces ExecutableInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def dimension (u : ℕ) : ℕ := rectangularInnerDimension u ^ 10

theorem dimension_ge (u : ℕ) : u ≤ dimension u := le_integerCeilRoot_pow (by decide)

theorem inner_positive (u : ℕ) (hu : 1 ≤ u) : 1 ≤ rectangularInnerDimension u :=
  le_integerCeilRoot (by decide) (by simpa using hu)

theorem inner_le (u : ℕ) : rectangularInnerDimension u ≤ u :=
  integerCeilRoot_le (by decide) (Nat.le_self_pow (by decide) u)

theorem dimension_le (u : ℕ) (hu : 1 ≤ u) : dimension u ≤ 1024 * u := by
  have hfloor : 1 ≤ integerFloorRoot 10 u := le_integerFloorRoot (by decide) (by simpa using hu)
  have hpow := integerFloorRoot_pow_le (degree := 10) (value := u) (by decide)
  unfold dimension rectangularInnerDimension integerCeilRoot
  simp only [show (10 : ℕ) ≠ 0 by decide, ↓reduceIte]
  split
  · rename_i he
    rw [he]
    omega
  · have hh : integerFloorRoot 10 u + 1 ≤ 2 * integerFloorRoot 10 u := by omega
    calc
      _ ≤ (2 * integerFloorRoot 10 u) ^ 10 := Nat.pow_le_pow_left hh 10
      _ = 1024 * integerFloorRoot 10 u ^ 10 := by rw [mul_pow]; norm_num
      _ ≤ 1024 * u := Nat.mul_le_mul_left 1024 hpow

def left (r : RectangularProductRequest) : BitMatrix (dimension r.dimension) (rectangularInnerDimension r.dimension) :=
  fun row inner => if h : row.val < r.dimension then r.left ⟨row.val, h⟩ inner else false

def right (r : RectangularProductRequest) : BitMatrix (rectangularInnerDimension r.dimension) (dimension r.dimension) :=
  fun inner col => if h : col.val < r.dimension then r.right inner ⟨col.val, h⟩ else false

def request (r : RectangularProductRequest) (hr : 1 ≤ r.dimension) : ExactPowerRequest where
  inner := rectangularInnerDimension r.dimension
  positive := inner_positive _ hr
  left := left r
  right := right r

theorem product_crop (r : RectangularProductRequest) (row col : Fin r.dimension) :
    integerMatrixProduct (left r) (right r) (row.castLE (dimension_ge r.dimension)) (col.castLE (dimension_ge r.dimension)) =
      integerMatrixProduct r.left r.right row col := by
  simp [integerMatrixProduct, left, right, row.isLt, col.isLt]

theorem padded_left {r : RectangularProductRequest} (row : Fin (dimension r.dimension))
    (inner : Fin (rectangularInnerDimension r.dimension)) (h : r.dimension ≤ row.val) : left r row inner = false := by
  simp [left, Nat.not_lt.mpr h]

theorem padded_right {r : RectangularProductRequest} (col : Fin (dimension r.dimension))
    (inner : Fin (rectangularInnerDimension r.dimension)) (h : r.dimension ≤ col.val) : right r inner col = false := by
  simp [right, Nat.not_lt.mpr h]

end NearCubicWires.RepairOrdinary.WilliamsPaddedRequest
