import Proof.Assembly.ClosureHardwireCacheLoop

/-! Eliminate every per-child byte/magnitude premise from the physical cache
loop by using the ORIGINAL cache length. This is measured before replication. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.OriginalCacheBounds
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
open RepairRepresentation SupplierPipeline SupplierEstimator ThresholdCompiler
open RepairSource.VerifierDecoding SupplierPrime
open scoped BigOperators

def capacity {q : Nat} (gs : List (ExactThresholdGate q)) := (exactListWord gs).length+2
def width {q : Nat} (gs : List (ExactThresholdGate q)) := (exactListWord gs).length+1

theorem bytes {q : Nat} (gs : List (ExactThresholdGate q)) :
    ∀ g∈gs,(exactWord g).length+2≤capacity gs := by
  intro g hg
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hg
  exact Nat.add_le_add_right (RowCachedCoordinateBounds.child_bytes gs i hi) 2

theorem magnitude {q : Nat} (gs : List (ExactThresholdGate q)) :
    ∀ g∈gs,g.target.natAbs+(∑ i,(g.weight i).natAbs)<2^width gs := by
  intro g hg
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hg
  have h := RowCachedEquation.cache_radix_safe gs ⟨i,hi⟩
  simpa only [equationMagnitudeBound,RowCachedEquation.equation,RowCachedCoordinateBounds.width,width,
    Nat.add_comm] using h

theorem run {q : Nat} (live : Finset (Fin q)) (y : BitInput live.card)
    (gs : List (ExactThresholdGate q)) (out : List Bool) :
    ∃ actual,runFrom HardwireCacheLoop.machine (HardwireCacheLoop.budget gs (capacity gs) (width gs))
      (RepeatMachine.cfg 0 (HardwireCacheLoop.entry live y gs (capacity gs) (width gs) 0 out) gs.length 1)=some actual ∧
      actual.final=RepeatMachine.cfg 3
        (HardwireCacheLoop.entry live y gs (capacity gs) (width gs) gs.length
          (out++gs.flatMap (fun g=>exactWord (RepairSource.CloseoutFinal.C10SupplierRowInput.hardwire live g y)))) gs.length 1 ∧
      actual.steps≤HardwireCacheLoop.budget gs (capacity gs) (width gs) :=
  HardwireCacheLoop.run live y gs (capacity gs) (width gs) (bytes gs)
    (by unfold width;omega) (magnitude gs) out

end NearCubicWires.P1Closure.OriginalCacheBounds
