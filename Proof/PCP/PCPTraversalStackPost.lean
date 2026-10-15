import Proof.PCP.PCPTraversalPost

/-! The checked return branches restore their logical outer stack prefixes;
the actually allocated zero tails remain explicit. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem resume_other (bits leftStack rightStack continuation : List Bool)
    (n cap leftCap rightZeros continuationZeros log : ℕ) (ambient : Fin 128 → List Bool)
    (i : Fin 128) (hi : i=0 ∨ i=2 ∨ i=78) :
    resumeRightOutput bits leftStack rightStack continuation n cap leftCap rightZeros continuationZeros log ambient i=ambient i := by
  rcases hi with rfl|rfl|rfl
  all_goals simp (disch := decide) only [resumeRightOutput,rightPopped,leftSaved,leftReturned,
    install_other,cleared_other]

theorem resume_left_stack (bits leftStack rightStack continuation : List Bool)
    (n cap leftCap rightZeros continuationZeros log : ℕ) (ambient : Fin 128 → List Bool) :
    resumeRightOutput bits leftStack rightStack continuation n cap leftCap rightZeros continuationZeros log ambient 82=
      ZeroPadding.pad leftCap (leftStack++(frame bits).reverse) := by
  simp (disch := decide) only [resumeRightOutput,rightPopped,install_other,cleared_other]
  exact install_slot saveLeftSlots saveLeftSlots_injective
    (cleared rightPushClearSlots cap log (leftReturned continuation continuationZeros ambient))
    (saveLeftLocal bits leftStack cap leftCap) 1

theorem resume_right_stack (bits leftStack rightStack continuation : List Bool)
    (n cap leftCap rightZeros continuationZeros log : ℕ) (ambient : Fin 128 → List Bool) :
    resumeRightOutput bits leftStack rightStack continuation n cap leftCap rightZeros continuationZeros log ambient 80=
      rightStack++List.replicate (2*n+1+rightZeros) false :=
  install_slot rightPopSlots rightPopSlots_injective
    (cleared rightPopClearSlots cap (max log (cap+1))
      (leftSaved bits leftStack cap leftCap log (leftReturned continuation continuationZeros ambient)))
    (rightPopLocal n cap rightZeros rightStack) 0

theorem resume_continuation (bits leftStack rightStack continuation : List Bool)
    (n cap leftCap rightZeros continuationZeros log : ℕ) (ambient : Fin 128 → List Bool) :
    resumeRightOutput bits leftStack rightStack continuation n cap leftCap rightZeros continuationZeros log ambient 81=
      continuation++true::true::List.replicate continuationZeros false := by
  simp (disch := decide) only [resumeRightOutput,rightPopped,leftSaved,install_other,cleared_other]
  exact install_slot ![81] (by decide) ambient
    (fun _ => continuation++true::true::List.replicate continuationZeros false) 0

theorem resume_driver (bits leftStack rightStack continuation : List Bool)
    (n cap leftCap rightZeros continuationZeros log : ℕ) (ambient : Fin 128 → List Bool) :
    resumeRightOutput bits leftStack rightStack continuation n cap leftCap rightZeros continuationZeros log ambient 28=
      List.replicate cap true := by
  simp (disch := decide) only [resumeRightOutput,rightPopped,install_cleared_driver]
theorem resume_log (bits leftStack rightStack continuation : List Bool)
    (n cap leftCap rightZeros continuationZeros log : ℕ) (ambient : Fin 128 → List Bool) :
    resumeRightOutput bits leftStack rightStack continuation n cap leftCap rightZeros continuationZeros log ambient 127=
      List.replicate (max log (cap+1)) false := by
  simp (disch := decide) only [resumeRightOutput,rightPopped,install_cleared_log]
  rw [max_eq_left (le_max_right log (cap+1))]

theorem combined_other (left right pre : List Bool) (cap z log : ℕ)
    (ambient : Fin 128 → List Bool) (first second : Fin 38 → List Bool)
    (i : Fin 128) (hi : i=0 ∨ i=2 ∨ i=78 ∨ i=80 ∨ i=81) :
    combinedOutput left right pre cap z log ambient first second i=ambient i := by
  rcases hi with rfl|rfl|rfl|rfl|rfl
  all_goals simp (disch := decide) only [combinedOutput,combinedTag,tagLoaded,tagPrinted,
    combinedInner,combineLoaded,leftPopped,pairResult_other,install_other,cleared_other]

theorem combined_left_stack (left right pre : List Bool) (cap z log : ℕ)
    (ambient : Fin 128 → List Bool) (first second : Fin 38 → List Bool) :
    combinedOutput left right pre cap z log ambient first second 82=
      pre++List.replicate (2*left.length+1+z) false := by
  simp (disch := decide) only [combinedOutput,combinedTag,tagLoaded,tagPrinted,
    combinedInner,combineLoaded,pairResult_other,install_other,cleared_other]
  exact install_slot leftPopSlots leftPopSlots_injective (cleared leftPopClearSlots cap log ambient)
    (leftPopLocal left pre cap z) 0

theorem combined_driver (left right pre : List Bool) (cap z log : ℕ)
    (ambient : Fin 128 → List Bool) (first second : Fin 38 → List Bool) :
    combinedOutput left right pre cap z log ambient first second 28=List.replicate cap true :=
  pairResult_driver cap (max log (cap+1)) _ (combinedTag left right pre cap z log ambient first) second
theorem combined_log (left right pre : List Bool) (cap z log : ℕ)
    (ambient : Fin 128 → List Bool) (first second : Fin 38 → List Bool) :
    combinedOutput left right pre cap z log ambient first second 127=List.replicate (max log (cap+1)) false := by
  have h := pairResult_log cap (max log (cap+1))
    (Nat.pair 2 (Nat.pair (RadixSemantics.value left) (RadixSemantics.value right))).bits
    (combinedTag left right pre cap z log ambient first) second
  rw [max_eq_left (le_max_right log (cap+1))] at h
  exact h

end NearCubicWires.RepairOrdinary.PCPTraversal
