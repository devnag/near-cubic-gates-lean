import Proof.PCP.PCPPNativeCapacity

/-! The selected common native bank supplies both literal-clause and
original normalized-query scalar bounds. Every value is physically emitted. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCapacityReady
open LocalBitMultitape PCPPNativeCapacityCold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def C (W : ℕ) := 16384*(W+1)^2
def F (W : ℕ) := 524288*(W+1)^2
def G (W : ℕ) := 67108864*(W+1)^3

theorem scalar_bounds (W : ℕ) :
    16384*(W+1)^2 ≤ C W ∧ 32*C W ≤ F W ∧ 64*(W+1)*(F W+1) ≤ G W := by
  have hpos : 1 ≤ (W+1)^2 := Nat.one_le_pow _ _ (by omega)
  refine ⟨le_rfl,by unfold C F; omega,?_⟩
  unfold F G
  rw [pow_succ]
  nlinarith [Nat.mul_le_mul_left (W+1) hpos]

theorem ready (W : ℕ) : ∃ out : Fin 61 → List Bool,
    ClockJoin.ReadyRun (PCPPNativeCapacityCold.machine 2 16384)
      (PCPPNativeCapacityCold.budget 2 16384 W) (PCPPNativeCapacityCold.input 2 W) out ∧
    out 0=List.replicate W true ∧ out 8=List.replicate (C W) true ∧
    out 28=List.replicate (F W) true ∧ out 50=List.replicate (G W) true := by
  obtain ⟨out,hr,hw,hvals⟩ := capacity_run 2 16384 W
  refine ⟨out,hr,hw,?_,?_,?_⟩
  · exact hvals 0
  · exact hvals 1
  · exact hvals 2

end NearCubicWires.RepairOrdinary.PCPPNativeCapacityReady
