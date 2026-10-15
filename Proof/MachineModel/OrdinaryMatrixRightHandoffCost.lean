import Proof.MachineModel.OrdinaryMatrixRightHandoff

/-! The complete coordinate/sort/right-plane handoff costs the number of
actual records and padded cells times a quadratic in the key width. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightHandoff
open LocalBitMultitape SupplierPrinter
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem original_length {U Used : ℕ} (payload : Fin Used → Fin (U+U) → Bool)
    (order : Fin Used → List (Fin (U+U)))
    (ho : ∀ inner,(order inner).Perm (List.finRange (U+U))) :
    (MatrixRightInputs.original payload order).length=Used*(U+U) := by
  have hl : ∀ inner,(order inner).length=U+U := by
    intro inner
    simpa using (ho inner).length_eq
  simp [MatrixRightInputs.original,List.length_flatMap,hl]

theorem budget_le (M U Used Capacity : ℕ) :
    budget M U Used Capacity (Used*(U+U)) ≤
      1024*(Used*(U+U)+Capacity*U+Used+1)*(M+M+2)^2 := by
  let N := Used*(U+U)
  let D := N+Capacity*U+Used+1
  let x := M+M+2
  have hND : N ≤ D := by dsimp [D]; omega
  have hD : 1 ≤ D := by dsimp [D]; omega
  have hx : x ≤ x^2 := by dsimp [x]; nlinarith
  have hx1 : 1 ≤ x^2 := (by dsimp [x]; omega : 1 ≤ x).trans hx
  have hc : 64*M+47 ≤ 32*x := by dsimp [x]; omega
  have hp : N*(64*M+47) ≤ 32*D*x^2 := by
    calc
      _ ≤ D*(32*x) := Nat.mul_le_mul hND hc
      _ = 32*D*x := by ring
      _ ≤ 32*D*x^2 := Nat.mul_le_mul_left (32*D) hx
  have hd1 : 1 ≤ D*x^2 := by nlinarith only [hD,hx1]
  change (2*(N*(64*M+47)+3)+2)+1+512*D*x^2 ≤ 1024*D*x^2
  nlinarith only [hp,hd1]

end NearCubicWires.RepairOrdinary.MatrixRightHandoff
