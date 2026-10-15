import Proof.MachineModel.OrdinaryMatrixCoefficientBitBody

/-! The mask bit read from an actual canonical coefficient frame is exactly
its natural absolute-value bit with the requested sign. Both false and true
bits are emitted; the selected position comes from the physical offset tape. -/
namespace NearCubicWires.RepairOrdinary.MatrixCoefficientBitCanonical
open LocalBitMultitape MatrixScoreBatch SignedSortKey
open MatrixCoefficientBitLeaf (cfg)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def signMatch (negative : Bool) (z : ℤ) := decide (z<0)==negative
def value (negative : Bool) (t : ℕ) (z : ℤ) := signMatch negative z && z.natAbs.testBit t
def budget (p : ℕ) := 4*p+12

theorem bit_run (negative flag : Bool) (p t : ℕ) (ht : t<p) (z : ℤ) (pre suffix out : List Bool) : ∃ actual,
    runFrom (MatrixCoefficientBitBody.machine negative) (budget p)
      (cfg (MatrixCoefficientBitBody.machine negative).start (pre++frame (signMagnitude p z)++suffix)
        pre.length (2*t) flag out)=some actual ∧
    actual.final=cfg actual.final.control (pre++frame (signMagnitude p z)++suffix)
      (pre.length+(frame (signMagnitude p z)).length) (2*t) (signMatch negative z) (out++[value negative t z]) ∧
    actual.steps≤budget p := by
  let bits := binary p z.natAbs
  have hi : t<bits.length := by simpa [bits] using ht
  have hs := List.take_append_drop t bits
  rw [List.drop_eq_getElem_cons hi] at hs
  have hv : bits[t]=z.natAbs.testBit t := MatrixScoreCanonical.binary_testBit p z.natAbs t ht
  rw [hv] at hs
  have hb : (bits.take t).length=t := by simp [List.length_take,Nat.min_eq_left (Nat.le_of_lt hi)]
  have ha : (bits.drop (t+1)).length=p-(t+1) := by simp [bits]
  obtain ⟨actual,hr,hf,hsteps⟩ := MatrixCoefficientBitBody.coefficient_run negative flag (decide (z<0))
    (z.natAbs.testBit t) (bits.take t) (bits.drop (t+1)) pre suffix out
  have hword : frame (decide (z<0)::(bits.take t++z.natAbs.testBit t::bits.drop (t+1)))=frame (signMagnitude p z) := by
    rw [hs]
    rfl
  rw [hword,hb] at hr hf
  have hc : MatrixCoefficientBitBody.budget (bits.take t) (bits.drop (t+1))≤budget p := by
    unfold MatrixCoefficientBitBody.budget budget
    rw [hb,ha]
    omega
  have he := runFrom_moreFuel (MatrixCoefficientBitBody.machine negative) _
    (budget p-MatrixCoefficientBitBody.budget (bits.take t) (bits.drop (t+1))) _ actual hr
  rw [Nat.add_sub_of_le hc] at he
  exact ⟨actual,he,hf,hsteps.trans_le hc⟩

end NearCubicWires.RepairOrdinary.MatrixCoefficientBitCanonical
