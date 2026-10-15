import Proof.Hierarchy.CompetitorSelectedRequestCountFocus

namespace NearCubicWires.RepairOrdinary.CompetitorSelectedRequestCount
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey
open MatrixScoreBatch CompetitorSelectedCount CompetitorCountMask
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem dock {s : ℕ} (firstMachine : Machine 91 s) (prefixBudget : ℕ)
    (r : Request) (Q : ℕ) (xs : List (Bool × ℕ)) (hn : xs.length≤r.U*r.U)
    (hx : ∀ x∈selected xs,x<2^Q) (initial : Fin 91 → List Bool) (out : Fin 78 → List Bool)
    (hp : ClockJoin.ReadyRun firstMachine prefixBudget initial (prepared Q xs out))
    (h0 : out 0=MatrixScoreBatch.physicalInput r)
    (ht : ∀ i,out (CompetitorSelectedRequestDrivers.outputSlots i)=
      CompetitorSelectedDimensions.outputWords Q (extraWidth r) (r.U*r.U) i) : ∃ actual,
    run (Composition.machine firstMachine last)
      (prefixBudget+1+coldBudget Q (scalarWidth r Q) (r.U*r.U)) initial=some actual ∧
      actual.steps≤prefixBudget+1+coldBudget Q (scalarWidth r Q) (r.U*r.U) ∧
      actual.final.heads=outputHeads Q (r.U*r.U) ∧
      actual.final.tapes 86=frame (binary (scalarWidth r Q) (selected xs).sum) ∧
      actual.final.tapes 76=List.replicate (scalarWidth r Q) true ∧
      actual.final.tapes 0=MatrixScoreBatch.physicalInput r := by
  obtain ⟨pre,hp,pt,ph,ps⟩ := hp
  obtain ⟨child,hc,cs,ch,c15,c12⟩ := cold_run Q (scalarWidth r Q) (r.U*r.U) xs hn
    (by unfold scalarWidth;omega) hx (scalar_fit r Q xs hn hx)
  obtain ⟨tail,hl,ts,th,t86,t76,t0⟩ := focus_run coldMachine
    (coldBudget Q (scalarWidth r Q) (r.U*r.U)) Q (r.U*r.U) (scalarWidth r Q)
    (selected xs).sum (MatrixScoreBatch.physicalInput r) pre.final.heads pre.final.tapes
    (shortTapes Q (scalarWidth r Q) (r.U*r.U) xs) ph
    (by intro i;rw [pt];exact projected_input r Q xs hn out ht i)
    (by rw [pt];exact h0) child hc cs ch c15 c12
  have hj := Composition.run_join firstMachine last _ _ _ pre tail hp hl
  refine ⟨Composition.joinedReceipt pre tail,hj,?_,th,t86,t76,t0⟩
  change pre.steps+1+tail.steps≤prefixBudget+1+coldBudget Q (scalarWidth r Q) (r.U*r.U)
  omega

end NearCubicWires.RepairOrdinary.CompetitorSelectedRequestCount
