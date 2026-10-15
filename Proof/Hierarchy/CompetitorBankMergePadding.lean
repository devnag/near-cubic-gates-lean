import Proof.Hierarchy.CompetitorBankMergeEntry

/-! The cell count at the actual native endpoint has a finite zero tail.
Transport the executed cold pass on exactly that retained driver. -/
namespace NearCubicWires.RepairOrdinary.CompetitorBankMerge
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def driverPadding (d : ℕ) : Fin 48 → ℕ := fun i => if i=27 then d else 0
def paddedInput (d w n : ℕ) (left right : List Bool) : Fin 48 → List Bool :=
  fun i => ZeroPadding.pad (driverPadding d i) (readyInput w n left right i)

theorem padded_run (d w : ℕ) (xs : List Pair) (suffixA suffixB : List Bool)
    (hv : ∀ a∈xs,Valid w a.1 a.2) :
    ∃ out,ClockJoin.ReadyRun machine (budget w xs.length)
      (paddedInput d w xs.length (leftWords w xs++suffixA) (rightWords w xs++suffixB)) out ∧
      out 8=mergedWords w xs ∧ out 19=leftWords w xs++suffixA ∧ out 23=rightWords w xs++suffixB ∧
      out 9=List.replicate w true ∧ out 27=ZeroPadding.pad d (CompareMachine.word xs.length) := by
  obtain ⟨produced,⟨base,hr,ht,hh,hs⟩,h8,h19,h23,h9,h27⟩ := ready_run w xs suffixA suffixB hv
  obtain ⟨r,hrun,hf,hsteps,_⟩ := ZeroPadding.run_config machine (driverPadding d) _ _ base hr
  refine ⟨r.final.tapes,⟨r,hrun,rfl,?_,hsteps.trans_le hs⟩,?_,?_,?_,?_,?_⟩
  · intro i
    rw [hf]
    exact hh i
  all_goals simp [hf,ZeroPadding.config,ht,driverPadding,h8,h19,h23,h9,h27]

theorem budget_bound (w n : ℕ) : budget w n≤200000*(n+1)*(w+1)^2 := by
  have hd := CompetitorDimensions.budget_bound w
  have hw : w≤(w+1)^2 := by nlinarith
  have hu : 1≤(w+1)^2 := by nlinarith
  have hnw := Nat.mul_le_mul_left n hw
  have hnu := Nat.mul_le_mul_left n hu
  unfold budget runBudget CompetitorResidueTable.coldPrepareBudget loopBudget bodyBudget fieldBudget
    capacity CompetitorResidueTable.capacity CompetitorReusableDecision.capacity at *
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorBankMerge
