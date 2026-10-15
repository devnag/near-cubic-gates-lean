import Proof.PCP.PCPTraversalCombineReturn

/-! Exact stack and retained-cursor postconditions of the checked enclosing
branches. These connect their executions to the common subtree invariant. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem descend_other (n cap countCap rightCap continuationCap log : ℕ)
    (rightStack continuation : List Bool) (ambient : Fin 128 → List Bool) (i : Fin 128)
    (hi : i=0 ∨ i=2 ∨ i=78 ∨ i=82) :
    descendOutput n cap countCap rightCap continuationCap log rightStack continuation ambient i=ambient i := by
  rcases hi with rfl|rfl|rfl|rfl
  all_goals simp (disch := decide) only [descendOutput,leftCopied,descendContinued,continuationPushed,
    descendPushed,rightPushed,splitOutput,cleared_other,install_other]

theorem descend_right_stack (n cap countCap rightCap continuationCap log : ℕ)
    (rightStack continuation : List Bool) (ambient : Fin 128 → List Bool) :
    descendOutput n cap countCap rightCap continuationCap log rightStack continuation ambient 80=
      ZeroPadding.pad rightCap (rightStack++(frame (List.replicate (n/2) true)).reverse) := by
  simp (disch := decide) only [descendOutput,leftCopied,descendContinued,continuationPushed,
    descendPushed,cleared_other,install_other,right_push_stack]

theorem descend_continuation (n cap countCap rightCap continuationCap log : ℕ)
    (rightStack continuation : List Bool) (ambient : Fin 128 → List Bool) :
    descendOutput n cap countCap rightCap continuationCap log rightStack continuation ambient 81=
      ZeroPadding.pad continuationCap (continuation++[false,true]) := by
  simp (disch := decide) only [descendOutput,leftCopied,install_cleared_other]
  exact install_slot ![81] (by decide)
    (descendPushed n cap countCap rightCap log rightStack ambient)
    (fun _ => ZeroPadding.pad continuationCap (continuation++[false,true])) 0

theorem descend_driver (n cap countCap rightCap continuationCap log : ℕ)
    (rightStack continuation : List Bool) (ambient : Fin 128 → List Bool) :
    descendOutput n cap countCap rightCap continuationCap log rightStack continuation ambient 28=List.replicate cap true := by
  simp (disch := decide) only [descendOutput,leftCopied,install_cleared_driver]

theorem descend_log (n cap countCap rightCap continuationCap log : ℕ)
    (rightStack continuation : List Bool) (ambient : Fin 128 → List Bool) :
    descendOutput n cap countCap rightCap continuationCap log rightStack continuation ambient 127=
      List.replicate (max log (cap+1)) false := by
  simp (disch := decide) only [descendOutput,leftCopied,install_cleared_log]
  rw [max_eq_left (le_max_right log (cap+1))]

end NearCubicWires.RepairOrdinary.PCPTraversal
