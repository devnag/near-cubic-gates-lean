import Proof.Amplification.RecoveryNestedTableWhole

namespace NearCubicWires.RepairOrdinary.RecoveryNestedTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStructure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem row_budgets_le (width limit : Nat) (hl : limit ≤ 3*(width+1)) :
    tableRowBudget width limit ≤ 10000000*(width+1)^2 ∧
      RecoveryOuterLeaf.tableBudget width limit ≤ 10000000*(width+1)^2 := by
  have hw : 32*width+53 ≤ 53*(width+1) := by omega
  have hlook : 6*limit*(32*width+53) ≤ 954*(width+1)^2 := by
    calc
      _ ≤ 6*(3*(width+1))*(53*(width+1)) := by gcongr
      _ = _ := by ring
  have hlook4 : 4*limit*(32*width+53) ≤ 6*limit*(32*width+53) := by gcongr; omega
  have hunit : width+1 ≤ (width+1)^2 := by nlinarith
  constructor
  · unfold tableRowBudget
    nlinarith
  · unfold RecoveryOuterLeaf.tableBudget
    nlinarith

theorem budgets_le (width limit innerCount outerCount : Nat)
    (hl : limit ≤ 3*(width+1)) (hi : innerCount ≤ limit) (ho : outerCount ≤ limit) :
    RecoveryRowTable.returnBudget width limit innerCount+
      (RecoveryOuterRoot.wholeBudget width limit outerCount+1+1)+2 ≤ 134217728*(width+1)^3 := by
  obtain ⟨hrow,houter⟩ := row_budgets_le width limit hl
  have hin : innerCount*(tableRowBudget width limit+3) ≤
      3*(width+1)*(10000000*(width+1)^2+3) := by gcongr; exact hi.trans hl
  have hout : outerCount*(RecoveryOuterLeaf.tableBudget width limit+3) ≤
      3*(width+1)*(10000000*(width+1)^2+3) := by gcongr; exact ho.trans hl
  have hlook : 2*outerCount*(32*width+53) ≤ 318*(width+1)^2 := by
    calc
      _ ≤ 2*(3*(width+1))*(53*(width+1)) := by gcongr; exact ho.trans hl; omega
      _ = _ := by ring
  have hunit : width+1 ≤ (width+1)^2 := by nlinarith
  have hpow : (width+1)^2 ≤ (width+1)^3 := by
    calc
      _ = 1*(width+1)^2 := by ring
      _ ≤ (width+1)*(width+1)^2 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  unfold RecoveryRowTable.returnBudget RecoveryOuterRoot.wholeBudget RecoveryOuterRoot.rootBudget RecoveryOuterTable.returnBudget
  nlinarith

theorem budget_le (x : State) (limit : Nat) (word innerBits outerBits innerPre outerPre : List Bool)
    (hx : Prepared x limit word innerBits outerBits innerPre outerPre)
    (hl : limit ≤ 3*(x.inner.base.state.bits.length+1)) :
    budget x limit ≤ 134217728*(x.inner.base.state.bits.length+1)^3 := by
  unfold budget
  rw [hx.copiedWidth]
  exact budgets_le _ _ _ _ hl hx.innerBound hx.outerBound

end NearCubicWires.RepairOrdinary.RecoveryNestedTable
