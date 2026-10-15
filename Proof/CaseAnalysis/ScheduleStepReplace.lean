import Proof.CaseAnalysis.ScheduleStepWrites

/-! The fitting-candidate branch physically clears the previous best and
copies the actual newly computed source length. Every other port survives. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Step
open LocalBitMultitape RepairOrdinary RecoveryRootRound ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def replace (sources : EightSources) (k D : Nat) :=
  Composition.machine (eraseBest sources k D) (copyBest sources k D)

theorem replace_run (sources : EightSources) (k D C N : Nat)
    (ambient : Fin (tapes sources k D)→List Bool) (hN : N+2 ≤ C)
    (hb : (ambient (port sources k D 2)).length ≤ C)
    (hd : ambient (port sources k D 3)=List.replicate C true)
    (hl : ambient (port sources k D 4)=List.replicate (C+1) false)
    (ht : ambient (bestSlots sources k D 0)=ZeroPadding.pad C (UnaryTemplate.tape N))
    (hc : ambient (copyLog sources k D 2)=List.replicate C false) :
    ClockJoin.ReadyRun (replace sources k D) ((2*C+4)+1+(2*N+6)) ambient
      (Function.update ambient (port sources k D 2) (ZeroPadding.pad C (List.replicate N true))) := by
  have he:=Reusable.erase_one (eraseBestSlots sources k D) (small_injective sources k D).2.2.2 C ambient hb hd hl
  let middle:=Function.update ambient (port sources k D 2) (List.replicate C false)
  change ClockJoin.ReadyRun (eraseBest sources k D) _ ambient middle at he
  have hi:=(small_injective sources k D).2.2.1
  have h01 : bestSlots sources k D 0≠port sources k D 2 := by
    change bestSlots sources k D 0≠bestSlots sources k D 1
    intro heq;have hbad:=hi heq;contradiction
  have hcopy:=Reusable.copy_into (bestSlots sources k D) hi C C N hN middle (by
      dsimp only [middle]
      rw [Function.update_of_ne h01]
      exact ht)
    (by change Function.update ambient (port sources k D 2) _ (port sources k D 2)=_;simp)
    (by
      change middle (copyLog sources k D 2)=_
      dsimp only [middle]
      rw [Function.update_of_ne (show copyLog sources k D 2≠port sources k D 2 from
        port_away sources k D ((2 : Fin 3).natAdd (Test.tapes sources k D)) 2)]
      exact hc)
  have hfinal : Function.update middle (port sources k D 2) (ZeroPadding.pad C (List.replicate N true))=
      Function.update ambient (port sources k D 2) (ZeroPadding.pad C (List.replicate N true)) := by
    funext i
    by_cases hi : i=port sources k D 2
    · subst i;simp
    · dsimp only [middle]
      rw [Function.update_of_ne hi,Function.update_of_ne hi,Function.update_of_ne hi]
  change ClockJoin.ReadyRun (copyBest sources k D) _ middle
    (Function.update middle (port sources k D 2) (ZeroPadding.pad C (List.replicate N true))) at hcopy
  rw [hfinal] at hcopy
  exact ClockJoin.join _ _ _ _ _ _ _ he hcopy

end
end NearCubicWires.RepairSource.CloseoutSchedule.Step
