import Proof.Circuits.DecompositionPrepare

/-! Resource ledger for the actual cold native count/capacity prefix. Arity
is explicitly charged, including the empty-child case. -/
namespace NearCubicWires.RepairOrdinary.DecompositionResource
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem natural_budget (n : ℕ) : PCPPQueryNatural.budget n ≤ 128*(n+1)^2 := by
  have h := DecompositionSource.Count.budget_bound n
  unfold DecompositionSource.Count.budget at h
  omega

theorem input_budget (a m N : ℕ) (tail : List Bool)
    (hN : (DecompositionInputCounts.word a m tail).length ≤ N) (hm : m ≤ N) :
    DecompositionInputDrivers.budget a m tail ≤ 512*(a+N+1)^2 := by
  have ha : a+1 ≤ a+N+1 := by omega
  have hm' : m+1 ≤ a+N+1 := by omega
  have hZ : 1 ≤ (a+N+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hL : (DecompositionInputCounts.word a m tail).length ≤ (a+N+1)^2 := by nlinarith
  have hba := (natural_budget a).trans (show 128*(a+1)^2 ≤ 128*(a+N+1)^2 by gcongr)
  have hbm := (natural_budget m).trans (show 128*(m+1)^2 ≤ 128*(a+N+1)^2 by gcongr)
  have hp : (a+1)*(m+1) ≤ (a+N+1)^2 := by
    calc
      _ ≤ (a+N+1)*(a+N+1) := Nat.mul_le_mul ha hm'
      _ = _ := by ring
  have hc := (DecompositionCountDrivers.budget_bound a m).trans
    (show 64*(a+1)*(m+1)+64 ≤ 64*(a+N+1)^2+64 by nlinarith)
  unfold DecompositionInputDrivers.budget DecompositionInputCounts.budget DecompositionCountReady.budget
  nlinarith

theorem cold_budget (D C a m N : ℕ) (tail : List Bool)
    (hN : (frame (DecompositionInputCounts.word a m tail)).length=N) (hm : m ≤ N) :
    DecompositionColdPrepare.budget D C a m tail ≤
      PCPSerializerCapacity.coefficient D C*(N+1)^(D+1)+512*(a+N+1)^2+4 := by
  have hw : (DecompositionInputCounts.word a m tail).length ≤ N := by
    rw [frame_length] at hN
    omega
  have hp := input_budget a m N tail hw hm
  have hc := PCPSerializerCapacity.budget_bound D C N
  unfold DecompositionColdPrepare.budget DecompositionCapacity.budget
  rw [hN]
  omega

end NearCubicWires.RepairOrdinary.DecompositionResource
