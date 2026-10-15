import Proof.Hierarchy.CompetitorSelectedRequestCountHeads

namespace NearCubicWires.RepairOrdinary.CompetitorSelectedRequestCount
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey
open MatrixScoreBatch CompetitorSelectedCount CompetitorCountMask
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem focus_run {s : ℕ} (childMachine : Machine 20 s) (fuel Q N w total : ℕ)
    (sourceWord : List Bool) (ah : Fin 91 → ℕ) (atapes : Fin 91 → List Bool)
    (inputData : Fin 20 → List Bool) (ph : ∀ i,ah i=0)
    (ht : ∀ i,atapes (slots i)=inputData i) (h0 : atapes 0=sourceWord)
    (child : ExecutionReceipt 20 s) (hc : run childMachine fuel inputData=some child)
    (cs : child.steps≤fuel) (ch : child.final.heads=finalHeads Q N)
    (c15 : child.final.tapes 15=frame (binary w total))
    (c12 : child.final.tapes 12=List.replicate w true) : ∃ tail,
    runFrom (RecoveryFocus.machine slots childMachine) fuel
      (RecoveryCalls.restarted (RecoveryFocus.machine slots childMachine) ah atapes)=some tail ∧
      tail.steps≤fuel ∧ tail.final.heads=outputHeads Q N ∧
      tail.final.tapes 86=frame (binary w total) ∧
      tail.final.tapes 76=List.replicate w true ∧ tail.final.tapes 0=sourceWord := by
  let entry := initialConfiguration childMachine inputData
  have hi : RecoveryFocus.config slots ah atapes entry=
      RecoveryCalls.restarted (RecoveryFocus.machine slots childMachine) ah atapes := by
    exact WilliamsSourceCrop.focus_same slots
      (RecoveryCalls.restarted (RecoveryFocus.machine slots childMachine) ah atapes) entry
      (fun i => ph (slots i)) ht
  obtain ⟨tail,hl,tf,ts⟩ := RecoveryFocus.run_config slots slots_injective childMachine
    ah atapes _ entry child hc
  rw [hi] at hl
  refine ⟨tail,hl,ts.trans_le cs,?_,?_,?_,?_⟩
  · exact (congrArg Configuration.heads tf).trans (focus_heads Q N ah atapes child.final ph ch)
  · apply (congrArg (fun c => c.tapes 86) tf).trans
    have hpick : RecoveryFocus.pick slots 86=some 15 := RecoveryFocus.pick_slot slots slots_injective 15
    simpa only [RecoveryFocus.config,hpick] using c15
  · apply (congrArg (fun c => c.tapes 76) tf).trans
    have hpick : RecoveryFocus.pick slots 76=some 12 := RecoveryFocus.pick_slot slots slots_injective 12
    simpa only [RecoveryFocus.config,hpick] using c12
  · apply (congrArg (fun c => c.tapes 0) tf).trans
    have hpick : RecoveryFocus.pick slots 0=none := by decide
    simpa only [RecoveryFocus.config,hpick] using h0

end NearCubicWires.RepairOrdinary.CompetitorSelectedRequestCount
