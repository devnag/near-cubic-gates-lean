import Proof.MachineModel.ClosureRadixNative

/-! A.12 preparation is additive. This explicit capacity bound exposes every
exponential factor: a fixed power of the replicated cache size, and the
existing digit-enumeration factor. No residual-table factor occurs here. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.CompactPreparationCost
open RepairRepresentation RepairOrdinary ExtIncidence

theorem capacity_bound {n : Nat} (gs : List (ExactThresholdGate n)) [P1Radix gs]
    (Q w X : Nat) (hn : n≤X) (hN : gs.length≤X)
    (hcache : (exactListWord gs).length≤X) (hb : P1Radix.bits gs≤X)
    (hp : P1CompactNativeWidth.width gs Q≤X) (hQ : Q≤X) (hw : w≤X) :
    P1CompactNativeMeasured.capacity gs Q w ≤
      2^84*(X+1)^16*2^(w*(Q+1)) := by
  have h1 : X+1 ≤ (X+1)^2 := by nlinarith
  have h2 : (X+1)^2 ≤ (X+1)^4 := by nlinarith [sq_nonneg ((X+1)^2-1 : Int)]
  have size : RowCachedCoordinateBounds.size gs (P1Radix.bits gs) ≤ 4*(X+1)^2 := by
    unfold RowCachedCoordinateBounds.size
    calc
      _ ≤ X+(X+1)*(X+1)+X+1 := by gcongr
      _ ≤ 4*(X+1)^2 := by nlinarith
  have mult : gs.length*Q+1 ≤ (X+1)^2 := by
    have := Nat.mul_le_mul hN hQ
    nlinarith
  have allocation : P1CompactNativeAllocation.capacity gs Q ≤ 2^17*(X+1)^4 := by
    unfold P1CompactNativeAllocation.capacity P1CompactRowCommonBounds.capacity
    calc
      _ ≤ 16384*((X+1)^2)*(4*(X+1)^2)+16*X+64 := by gcongr
      _ ≤ 2^17*(X+1)^4 := by nlinarith [h1.trans h2]
  have scale : CloseoutRowsPreparationBounds.scale n (P1CompactNativeWidth.width gs Q)
      (P1CompactNativeAllocation.capacity gs Q) w gs.length Q ≤ 2^18*(X+1)^4 := by
    unfold CloseoutRowsPreparationBounds.scale
    nlinarith [h1.trans h2]
  change 4096*(CloseoutRowsPreparationBounds.scale n (P1CompactNativeWidth.width gs Q)
    (P1CompactNativeAllocation.capacity gs Q) w gs.length Q)^4*2^(w*(Q+1)) ≤ _
  calc
    _ ≤ 4096*(2^18*(X+1)^4)^4*2^(w*(Q+1)) := by gcongr
    _ = 2^84*(X+1)^16*2^(w*(Q+1)) := by ring

theorem load_margin (K w s : Nat) (hload : 200*(K+w*(K+2)) ≤ s) :
    10*(17*K+w*(K+2)) ≤ s := by omega

end NearCubicWires.P1Closure.CompactPreparationCost
