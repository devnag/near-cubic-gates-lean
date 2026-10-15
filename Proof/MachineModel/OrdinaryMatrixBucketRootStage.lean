import Proof.MachineModel.OrdinaryMatrixBucketRootClear

namespace NearCubicWires.RepairOrdinary.MatrixBucketRootStage
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch
open MatrixScoreReusableRanks (D)
open MatrixBucketRootClear (tapes scratchSlots)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 22) : Fin 27 := i.castAdd 5
theorem slots_injective : Function.Injective slots := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 27 => a.val) h)
theorem pick_fresh (i : Fin 5) : RecoveryFocus.pick slots (i.natAdd 22)=none := by
  fin_cases i <;> decide
noncomputable def last := RecoveryFocus.machine slots MatrixBucketDimensions.Power.machine
noncomputable def machine := Composition.machine MatrixBucketRootClear.machine last
def budget (r : Request) (c : ℕ) := (2*D r+4)+1+(WilliamsPower.budget 10 c+2)
noncomputable def input (r : Request) (c cap : ℕ) (work : Fin 23 → List Bool) :=
  RecoveryCalls.restarted machine (fun _ => 0) (tapes r c cap work)

theorem stage_run (r : Request) (c cap : ℕ) (work : Fin 23 → List Bool)
    (hb : ∀ i,(work i).length≤D r) (hc : 1≤c) (hroot : c≤MatrixBucketDimensions.capacity r.U) :
    ∃ actual,runFrom machine (budget r c) (input r c cap work)=some actual ∧
      actual.final.heads=(fun _ => 0) ∧
      actual.final.tapes 0=UnaryTemplate.tape c ∧
      actual.final.tapes 20=ZeroPadding.pad (D r) (List.replicate (c^10) true) ∧
      actual.final.tapes 22=UnaryTemplate.tape r.U ∧
      actual.final.tapes 23=List.replicate (D r) false ∧
      actual.final.tapes 24=List.replicate (D r) false ∧
      actual.final.tapes 25=List.replicate (D r) true ∧
      actual.final.tapes 26=List.replicate (max cap (D r+1)) false ∧
      (∀ i,(actual.final.tapes (scratchSlots i)).length≤D r) ∧ actual.steps≤budget r c := by
  obtain ⟨cleared,hclear,ch,ct,cs⟩ := MatrixBucketRootClear.clear_run r c cap work hb
  obtain ⟨base,hbase,bs,b0,b20,bh,bt⟩ := MatrixBucketRootPower.power_run r c hc hroot
  have ready : ClockJoin.ReadyRun MatrixBucketDimensions.Power.machine (WilliamsPower.budget 10 c+2)
      (MatrixBucketDimensions.Power.input c (D r)) base.final.tapes := ⟨base,hbase,rfl,bh,bs⟩
  obtain ⟨powered,hp,ph,pt,ps⟩ := CompetitorReusableDecision.bounded_focused_run slots slots_injective
    MatrixBucketDimensions.Power.machine _ _ ready (fun _ => 0)
    (tapes r c (max cap (D r+1)) (fun _ => List.replicate (D r) false))
    (by intro i; rfl) (by intro i; fin_cases i <;> rfl)
  have hi : Composition.restart cleared.final last.start=
      RecoveryCalls.restarted last (fun _ => 0)
        (tapes r c (max cap (D r+1)) (fun _ => List.replicate (D r) false)) := by
    apply configuration_ext
    · rfl
    · exact ch
    · exact ct
  change runFrom last (WilliamsPower.budget 10 c+2)
    (RecoveryCalls.restarted last (fun _ => 0)
      (tapes r c (max cap (D r+1)) (fun _ => List.replicate (D r) false)))=some powered at hp
  rw [←hi] at hp
  have joined := Composition.run_join MatrixBucketRootClear.machine last _ _ _ cleared powered hclear hp
  have localT (i : Fin 22) : powered.final.tapes (slots i)=base.final.tapes i := by
    rw [pt]
    exact install_slot slots slots_injective _ _ i
  have freshT (i : Fin 5) : powered.final.tapes (i.natAdd 22)=
      tapes r c (max cap (D r+1)) (fun _ => List.replicate (D r) false) (i.natAdd 22) := by
    rw [pt]
    simp only [install,pick_fresh]
  refine ⟨Composition.joinedReceipt cleared powered,joined,ph,(localT 0).trans b0,(localT 20).trans b20,
    freshT 0,freshT 1,freshT 2,freshT 3,freshT 4,?_,?_⟩
  · intro i
    change (powered.final.tapes (scratchSlots i)).length≤D r
    fin_cases i
    · exact (congrArg List.length (localT 1)).trans_le (bt 1)
    · exact (congrArg List.length (localT 2)).trans_le (bt 2)
    · exact (congrArg List.length (localT 3)).trans_le (bt 3)
    · exact (congrArg List.length (localT 4)).trans_le (bt 4)
    · exact (congrArg List.length (localT 5)).trans_le (bt 5)
    · exact (congrArg List.length (localT 6)).trans_le (bt 6)
    · exact (congrArg List.length (localT 7)).trans_le (bt 7)
    · exact (congrArg List.length (localT 8)).trans_le (bt 8)
    · exact (congrArg List.length (localT 9)).trans_le (bt 9)
    · exact (congrArg List.length (localT 10)).trans_le (bt 10)
    · exact (congrArg List.length (localT 11)).trans_le (bt 11)
    · exact (congrArg List.length (localT 12)).trans_le (bt 12)
    · exact (congrArg List.length (localT 13)).trans_le (bt 13)
    · exact (congrArg List.length (localT 14)).trans_le (bt 14)
    · exact (congrArg List.length (localT 15)).trans_le (bt 15)
    · exact (congrArg List.length (localT 16)).trans_le (bt 16)
    · exact (congrArg List.length (localT 17)).trans_le (bt 17)
    · exact (congrArg List.length (localT 18)).trans_le (bt 18)
    · exact (congrArg List.length (localT 19)).trans_le (bt 19)
    · exact (congrArg List.length (localT 20)).trans_le (bt 20)
    · exact (congrArg List.length (localT 21)).trans_le (bt 21)
    · have hh : powered.final.tapes 23=List.replicate (D r) false := freshT 1
      change (powered.final.tapes 23).length≤D r
      rw [hh,List.length_replicate]
    · have hh : powered.final.tapes 24=List.replicate (D r) false := freshT 2
      change (powered.final.tapes 24).length≤D r
      rw [hh,List.length_replicate]
  · change cleared.steps+1+powered.steps≤_
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixBucketRootStage
