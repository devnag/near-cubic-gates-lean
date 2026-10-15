import Proof.Hierarchy.CompetitorSelectedPaddingMeaning

/-! A selected residual-row total fits in a short field derived from the
original request. Its width contains log U, never the grid cardinality U². -/
namespace NearCubicWires.RepairOrdinary.CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extraWidth (r : Request) :=
  CompetitorPlaneWidth.width (natBitLength r.U) r.p+natBitLength r.U
def scalarWidth (r : Request) (Q : ℕ) := Q+extraWidth r

theorem extraWidth_eq (r : Request) : extraWidth r=2*r.d+2*r.p+4 := by
  have hb : natBitLength r.U=r.d+1 := by simp [Request.U,natBitLength,Nat.log_pow]
  unfold extraWidth CompetitorPlaneWidth.width
  rw [hb]
  omega

theorem list_sum_bound (Q : ℕ) (xs : List ℕ) (hx : ∀ x∈xs,x<2^Q) :
    xs.sum≤xs.length*2^Q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h0 := hx x (by simp)
    have h1 := ih (by intro y hy;exact hx y (by simp [hy]))
    simp only [List.sum_cons,List.length_cons]
    nlinarith

theorem scalar_fit (r : Request) (Q : ℕ) (xs : List (Bool × ℕ))
    (hn : xs.length≤r.U*r.U) (hx : ∀ x∈selected xs,x<2^Q) :
    (selected xs).sum<2^(scalarWidth r Q) := by
  have hs := list_sum_bound Q (selected xs) hx
  rw [selected_length] at hs
  have hg : r.U*r.U*2^Q=2^(2*r.d+Q) := by
    simp only [Request.U,←pow_add]
    congr 1
    omega
  have he : 2*r.d+Q<scalarWidth r Q := by rw [scalarWidth,extraWidth_eq];omega
  exact (hs.trans (Nat.mul_le_mul_right (2^Q) hn)).trans_lt
    (hg ▸ Nat.pow_lt_pow_right (by decide : 1<2) he)

theorem scalar_width_bound (r : Request) (Q : ℕ) (hq : Q≤r.p) :
    scalarWidth r Q≤4*(r.d+r.p+1) := by
  rw [scalarWidth,extraWidth_eq]
  omega

end NearCubicWires.RepairOrdinary.CompetitorSelectedCount
