import Proof.MachineModel.ClosureRawRelabelRun
import Proof.MachineModel.ClosureRawRelabelCost

/-! One uniform capacity and budget for all live-assignment indices yi≤Y.
Only the real lowered-stream length bound S remains to be instantiated;
no output-prefix length or residual-table factor enters this syntax cost. -/
namespace NearCubicWires.P1Closure.RawRelabelUniform
open LocalBitMultitape ExtDecompositionBatch ExtIncidence
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (N Y : ℕ):=N*Y+2
def logCapacity (N Y S : ℕ):=(2*(N*Y+1)+4)*S+RawRelabelOffset.rawBudget N Y
def budget (N Y S : ℕ):=
  RawRelabelOffset.budget N Y+2*((2*(N*Y+1)+4)*S)+2*capacity N Y+12

theorem bounds (N yi Y S : ℕ) (P : List (List ℕ)) (hy : yi≤Y) (hS : (stream P).length≤S) :
    N*yi+2≤capacity N Y ∧
    RawRelabelOffset.rawBudget N yi≤logCapacity N Y S ∧
    RawRelabelMachine.budget (N*yi+1) P≤logCapacity N Y S ∧
    RawRelabelRun.budget N yi (capacity N Y) P≤budget N Y S := by
  have mul:=Nat.mul_le_mul_left N hy
  have offset:RawRelabelOffset.rawBudget N yi≤RawRelabelOffset.rawBudget N Y:=by
    unfold RawRelabelOffset.rawBudget
    exact Nat.add_le_add_right (Nat.mul_le_mul_left N (by omega)) 5
  have scan:= (RawRelabelCost.scan_bound (N*yi+1) P).trans
    (Nat.mul_le_mul (show 2*(N*yi+1)+4≤2*(N*Y+1)+4 by omega) hS)
  refine ⟨by unfold capacity;omega,?_,?_,?_⟩
  · unfold logCapacity;omega
  · unfold logCapacity;omega
  · unfold RawRelabelRun.budget budget RawRelabelOffset.budget
    omega

theorem run (N yi Y S : ℕ) (P : List (List ℕ)) (tail out : List Bool)
    (hy : yi≤Y) (hS : (stream P).length≤S) :
    let R:=capacity N Y
    let L:=logCapacity N Y S
    let result:=out++stream (P.map (List.map (fun c=>N*yi+c+1)))
    Step RawRelabelRun.machine (budget N Y S)
      (RawRelabelRun.heads out 0) (RawRelabelRun.input N yi R L (stream P++tail) out)
      (RawRelabelRun.heads result 0) (RawRelabelRun.input N yi R L (stream P++tail) result) := by
  obtain ⟨hR,hO,hL,hB⟩:=bounds N yi Y S P hy hS
  exact (RawRelabelRun.run N yi _ _ P tail out hR hO hL).enlarge hB

end NearCubicWires.P1Closure.RawRelabelUniform
