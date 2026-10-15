import Proof.CaseAnalysis.TouchingArithmeticBounds
import Mathlib.Tactic.Linarith

/-! Exact complement scores implement the unchanged touching comparison.
Already touched gates contribute zero; untouched gates add one binomial.
Thus the physical score fold needs addition and no per-gate subtraction. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Complement
open SupplierTouching
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def score {Coordinate Gate : Type} [DecidableEq Coordinate] [Fintype Gate]
    (support : Gate→Finset Coordinate) (selected undecided : Finset Coordinate) (k : ℕ):ℕ:=
  ∑ gate,if Disjoint selected (support gate) then Nat.choose (undecided\support gate).card k else 0

theorem score_partition {Coordinate Gate : Type} [DecidableEq Coordinate] [Fintype Gate]
    (support : Gate→Finset Coordinate) (selected undecided : Finset Coordinate) (k : ℕ):
    conditionalTouchNumerator support selected undecided k+score support selected undecided k=
      Fintype.card Gate*Nat.choose undecided.card k:=by
  classical
  rw [conditionalTouchNumerator,score,←Finset.sum_add_distrib]
  have each (gate : Gate):conditionalGateTouchCount selected undecided (support gate) k+
      (if Disjoint selected (support gate) then Nat.choose (undecided\support gate).card k else 0)=
        Nat.choose undecided.card k:=by
    unfold conditionalGateTouchCount
    split
    · exact Nat.sub_add_cancel (Nat.choose_le_choose k (Finset.card_le_card Finset.sdiff_subset))
    · exact Nat.add_zero _
  simp only [each]
  simp

theorem score_comparison {Coordinate Gate : Type} [DecidableEq Coordinate] [Fintype Gate]
    (support : Gate→Finset Coordinate) (selected undecided : Finset Coordinate) (coordinate : Coordinate) (k : ℕ):
    (conditionalTouchNumerator support (insert coordinate selected) undecided (k-1)*Nat.choose undecided.card k≤
      conditionalTouchNumerator support selected undecided k*Nat.choose undecided.card (k-1)) ↔
    (score support selected undecided k*Nat.choose undecided.card (k-1)≤
      score support (insert coordinate selected) undecided (k-1)*Nat.choose undecided.card k):=by
  have included:=score_partition support (insert coordinate selected) undecided (k-1)
  have excluded:=score_partition support selected undecided k
  have hi:=congrArg (fun n=>n*Nat.choose undecided.card k) included
  have he:=congrArg (fun n=>n*Nat.choose undecided.card (k-1)) excluded
  constructor <;> intro h <;> nlinarith [hi,he]

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Complement
