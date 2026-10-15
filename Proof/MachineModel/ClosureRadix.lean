import Proof.MachineModel.ClosureCompactBounds

/-! A.12's per-equation radix and per-monomial degree are independent of
cache cardinality. This is data supplied by the actual retained family;
its sole semantic premise is proved for the actual pool below. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.RepairOrdinary
open RepairRepresentation SupplierPipeline SupplierEstimator ThresholdCompiler SupplierPrime

class P1Radix {n : Nat} (gs : List (ExactThresholdGate n)) where
  bits : Nat
  positive : 0 < bits
  safe : ∀ i : Fin gs.length,
    equationMagnitudeBound (RowCachedEquation.equation gs[i.val]) < 2^bits
  degree : Nat

namespace P1Radix
variable {n : Nat} (gs : List (ExactThresholdGate n)) [inst : P1Radix gs]

theorem value_width (i : Nat) (hi : i < gs.length) (j : Nat) (hj : j ≤ n) :
    natBitLength (RowCachedCoordinateAppend.value gs i hi j hj).natAbs ≤ bits gs := by
  have hm : RowNativeCoordinate.value gs[i] j hj ∈ RowNativeCoordinate.fields gs[i] :=
    List.getElem_mem _
  have hb : (RowNativeCoordinate.value gs[i] j hj).natAbs ≤
      equationMagnitudeBound (RowCachedEquation.equation gs[i]) := by
    rcases List.mem_append.mp hm with hw | ht
    · obtain ⟨k,hk⟩ := List.mem_ofFn.mp hw
      rw [← hk]
      exact (Finset.single_le_sum (fun k _ => Nat.zero_le (gs[i].weight k).natAbs)
        (Finset.mem_univ k)).trans (Nat.le_add_right _ _)
    · have he := List.mem_singleton.mp ht
      rw [he]
      exact Nat.le_add_left _ _
  have hz : (RowCachedCoordinateAppend.value gs i hi j hj).natAbs < 2^bits gs :=
    hb.trans_lt (safe ⟨i,hi⟩)
  have hlog := Nat.log_lt_of_lt_pow' (by have := positive (gs := gs); omega) hz
  change Nat.log 2 (RowCachedCoordinateAppend.value gs i hi j hj).natAbs + 1 ≤ bits gs
  omega

end P1Radix

noncomputable abbrev p1ActualRadix {q : Nat} (a : DecompositionAlgorithm)
    (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (s : Nat)
    (harity : (s+1)/2+s/2 = liveᶜ.card) (degree : Nat) :
    P1Radix (RepairSource.CloseoutFinal.C10SupplierRowInput.pool a live occ s harity) where
  bits := P1Closure.CompactBounds.radix a live occ
  positive := by unfold P1Closure.CompactBounds.radix; omega
  safe := fun i => P1Closure.CompactBounds.pool_magnitude a live occ s harity _
    (List.getElem_mem i.isLt)
  degree := degree

end NearCubicWires.RepairOrdinary
