import Proof.Hierarchy.CompetitorSelectedRequestCountLayout
import Proof.Amplification.RecoveryFocusDock

/-! The original Request's physical dimension producer and selected SUM,
with only the live scalar endpoint required by the six-field consumer. The
program is exactly SelectedRequestCount.machine. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountRecordRequestInput
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey
open MatrixScoreBatch CompetitorSelectedCount CompetitorCountMask
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem selected_run (r : Request) (Q : ℕ) (xs : List (Bool × ℕ))
    (hn : xs.length≤r.U*r.U) (hx : ∀ x∈selected xs,x<2^Q) : ∃ actual,
    run CompetitorSelectedRequestCount.machine (CompetitorSelectedRequestCount.budget r Q)
      (CompetitorSelectedRequestCount.input r Q xs)=some actual ∧
      actual.steps≤CompetitorSelectedRequestCount.budget r Q ∧
      actual.final.tapes 86=frame (binary (scalarWidth r Q) (selected xs).sum) ∧
      actual.final.tapes 76=List.replicate (scalarWidth r Q) true ∧
      actual.final.heads 86=0 ∧ actual.final.heads 76=0 ∧
      actual.final.tapes 0=MatrixScoreBatch.physicalInput r := by
  obtain ⟨out,ho,h0,ht⟩ := CompetitorSelectedRequestDrivers.drivers_run r Q
  let ambient := CompetitorSelectedRequestCount.prepared Q xs out
  have hp : ClockJoin.ReadyRun CompetitorSelectedRequestCount.first
      (CompetitorSelectedRequestDrivers.budget r Q) (CompetitorSelectedRequestCount.input r Q xs) ambient :=
    ClockJoin.lift (e := 13) (Equiv.refl (Fin 91)) _ _ _ _ (CompetitorSelectedRequestCount.extra Q xs) ho
  obtain ⟨prepared,hp,pt,ph,ps⟩ := hp
  obtain ⟨child,hc,cs,ch,c15,c12⟩ := cold_run Q (scalarWidth r Q) (r.U*r.U) xs hn
    (by unfold scalarWidth;omega) hx (scalar_fit r Q xs hn hx)
  have hin : ∀ i,prepared.final.tapes (CompetitorSelectedRequestCount.slots i)=
      (initialConfiguration coldMachine (shortTapes Q (scalarWidth r Q) (r.U*r.U) xs)).tapes i := by
    intro i
    rw [pt]
    exact CompetitorSelectedRequestCount.projected_input r Q xs hn out ht i
  obtain ⟨tail,hl,_,ts,th,tt,keep⟩ := RecoveryFocus.dock CompetitorSelectedRequestCount.slots
    CompetitorSelectedRequestCount.slots_injective coldMachine _ prepared.final.heads prepared.final.tapes
    _ (fun i => ph _) hin child hc
  have hl' : runFrom CompetitorSelectedRequestCount.last (coldBudget Q (scalarWidth r Q) (r.U*r.U))
      (Composition.restart prepared.final CompetitorSelectedRequestCount.last.start)=some tail := hl
  have hj := Composition.run_join CompetitorSelectedRequestCount.first CompetitorSelectedRequestCount.last
    _ _ _ prepared tail hp hl'
  have h86 : tail.final.tapes 86=frame (binary (scalarWidth r Q) (selected xs).sum) := (tt 15).trans c15
  have h76 : tail.final.tapes 76=List.replicate (scalarWidth r Q) true := (tt 12).trans c12
  have hh86 : tail.final.heads 86=0 := (th 15).trans (by rw [ch]; rfl)
  have hh76 : tail.final.heads 76=0 := (th 12).trans (by rw [ch]; rfl)
  have hh0 : tail.final.tapes 0=MatrixScoreBatch.physicalInput r := by
    rw [(keep 0 (by decide)).2,pt]
    exact h0
  have hsteps : prepared.steps+1+tail.steps≤CompetitorSelectedRequestCount.budget r Q := by
    rw [ts]
    unfold CompetitorSelectedRequestCount.budget
    omega
  exact ⟨Composition.joinedReceipt prepared tail,hj,hsteps,h86,h76,hh86,hh76,hh0⟩

end NearCubicWires.RepairOrdinary.CompetitorCountRecordRequestInput
