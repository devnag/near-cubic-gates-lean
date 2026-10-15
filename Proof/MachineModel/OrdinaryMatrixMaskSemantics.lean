import Proof.MachineModel.OrdinaryMatrixMaskAndPass

/-! The masks actually emitted by gate-bit extraction and bucket expansion
match the signed left-matrix cells. This is the bridge consumed by the
physical AND pass before an actual Williams call. -/
namespace NearCubicWires.RepairOrdinary.MatrixMaskSemantics
open LocalBitMultitape MatrixScoreBatch SupplierPrinter
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def mask (r : Request) (negative : Bool) (t : ℕ) := MatrixMaskPad.output r.Buckets (r.Capacity-r.Used)
  (MatrixCoefficientBitNative.output r negative t)
def cell (r : Request) (negative : Bool) (t : ℕ) (inner : Fin r.Capacity) :=
  if hi : inner.val<r.Used then MatrixCoefficientBitCanonical.value negative t
    (weight r (finProdFinEquiv.symm (⟨inner.val,hi⟩ : Fin (r.Gates*r.Buckets))).1) else false

theorem coefficient_eq (negative : Bool) (z : ℤ) (t : ℕ) :
    LeftPlaneCell.coefficientBit negative z t=MatrixCoefficientBitCanonical.value negative t z := by
  cases negative <;> by_cases hz : z<0
  all_goals simp [LeftPlaneCell.coefficientBit,positiveMagnitudeBit,negativeMagnitudeBit,
    MatrixCoefficientBitCanonical.value,MatrixCoefficientBitCanonical.signMatch,hz,show (0≤z) ↔ ¬z<0 by omega]

theorem gate_bits_length (r : Request) (negative : Bool) (t : ℕ) :
    (MatrixCoefficientBitNative.output r negative t).length=r.Gates := by
  simp [MatrixCoefficientBitNative.output,MatrixCoefficientBitLoop.output,MatrixCoefficientBitNative.coefficients,Request.Gates]

theorem gate_bit (r : Request) (negative : Bool) (t : ℕ) (gate : Fin r.Gates) :
    (MatrixCoefficientBitNative.output r negative t)[gate.val]'(by rw [gate_bits_length]; exact gate.isLt)=
      MatrixCoefficientBitCanonical.value negative t (weight r gate) := by
  simp [MatrixCoefficientBitNative.output,MatrixCoefficientBitLoop.output,MatrixCoefficientBitNative.coefficients,weight,List.get_eq_getElem]

theorem expand_read (B : ℕ) (bits : List Bool) (k j : ℕ) (hk : k<bits.length) (hj : j<B) :
    readTapeBit (MatrixMaskExpand.output B bits) (k*B+j)=bits[k] := by
  induction bits generalizing k with
  | nil => simp at hk
  | cons bit bits ih =>
    cases k with
    | zero =>
      simp only [MatrixMaskExpand.output,List.flatMap_cons,Nat.zero_mul,Nat.zero_add,readTapeBit,List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by simpa using hj)]
      simp [hj]
    | succ k =>
      have hk' : k<bits.length := by simpa using hk
      simp only [MatrixMaskExpand.output,List.flatMap_cons,readTapeBit,List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by simp only [List.length_replicate,Nat.add_mul,Nat.one_mul]; omega)]
      have hi : (k+1)*B+j-B=k*B+j := by simp only [Nat.add_mul,Nat.one_mul]; omega
      simp only [List.length_replicate,hi,List.getElem_cons_succ]
      simpa only [readTapeBit,List.getD_eq_getElem?_getD,MatrixMaskExpand.output] using ih k hk'

theorem mask_length (r : Request) (negative : Bool) (t : ℕ) : (mask r negative t).length=r.Capacity := by
  simp only [mask,MatrixMaskPad.output,List.length_append,MatrixMaskExpand.output_length,List.length_replicate,gate_bits_length]
  exact Nat.add_sub_of_le (MatrixScoreBatch.capacity r)

theorem mask_read (r : Request) (negative : Bool) (t : ℕ) (inner : Fin r.Capacity) :
    readTapeBit (mask r negative t) inner.val=cell r negative t inner := by
  let bits := MatrixCoefficientBitNative.output r negative t
  have hlen : (MatrixMaskExpand.output r.Buckets bits).length=r.Used := by
    rw [MatrixMaskExpand.output_length,show bits.length=r.Gates from gate_bits_length r negative t]
    rfl
  unfold mask MatrixMaskPad.output
  change readTapeBit (MatrixMaskExpand.output r.Buckets bits++List.replicate (r.Capacity-r.Used) false) inner.val=cell r negative t inner
  by_cases hi : inner.val<r.Used
  · let pair := finProdFinEquiv.symm (⟨inner.val,hi⟩ : Fin (r.Gates*r.Buckets))
    have hpair : pair.1.val*r.Buckets+pair.2.val=inner.val := by
      change inner.val/r.Buckets*r.Buckets+inner.val%r.Buckets=inner.val
      simpa only [Nat.mul_comm] using Nat.div_add_mod inner.val r.Buckets
    have hgate : pair.1.val<bits.length := by rw [show bits.length=r.Gates from gate_bits_length r negative t]; exact pair.1.isLt
    have hread := expand_read r.Buckets bits pair.1.val pair.2.val hgate pair.2.isLt
    rw [hpair] at hread
    have hb : readTapeBit (MatrixMaskExpand.output r.Buckets bits++List.replicate (r.Capacity-r.Used) false) inner.val=
        readTapeBit (MatrixMaskExpand.output r.Buckets bits) inner.val := by
      simp only [readTapeBit,List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rw [hb,hread]
    change bits[pair.1.val]=_
    rw [show bits[pair.1.val]=MatrixCoefficientBitCanonical.value negative t (weight r pair.1) from gate_bit r negative t pair.1]
    simp only [cell,dif_pos hi,pair]
  · simp only [readTapeBit,List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [cell,hi,List.getElem?_replicate]
    split <;> rfl

theorem signed_cell (r : Request) (negative : Bool) (t : ℕ) (row : Fin r.U) (inner : Fin r.Capacity) :
    LeftPlaneCell.coefficientBit negative (signedLeft r row inner) t=
      (LeftPlaneCell.coefficientBit false
        (padSignedInner (Capacity := r.Capacity) (MatrixBucketLeftPlane.left r) row inner) 0 &&
        cell r negative t inner) := by
  by_cases hi : inner.val<r.Used
  · unfold Request.Used Request.Buckets at hi
    simp only [signedLeft,MatrixBucketLeftPlane.left,padSignedInner,cell,Request.Used,Request.Buckets,dif_pos hi]
    simp only [reindexedLaterBucketLeft,laterBucketLeft]
    split_ifs <;> simp [coefficient_eq,MatrixCoefficientBitCanonical.value,MatrixCoefficientBitCanonical.signMatch]
    rfl
  · unfold Request.Used Request.Buckets at hi
    simp [signedLeft,padSignedInner,hi,cell,Request.Used,Request.Buckets]

end NearCubicWires.RepairOrdinary.MatrixMaskSemantics
