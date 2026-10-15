import Proof.MachineModel.OrdinaryMatrixBucketRootStage
import Proof.Circuits.MatrixBucketDimensionsCompare

namespace NearCubicWires.RepairOrdinary.MatrixBucketRootTest
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch
open MatrixScoreReusableRanks (D)
open MatrixBucketRootClear (tapes scratchSlots)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 4 → Fin 27 := ![22,20,23,24]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def last := RecoveryFocus.machine slots MatrixBucketDimensions.Compare.machine
noncomputable def machine := Composition.machine MatrixBucketRootStage.machine last
def budget (r : Request) := 4*D r+20
noncomputable def input (r : Request) (c cap : ℕ) (work : Fin 23 → List Bool) :=
  RecoveryCalls.restarted machine (fun _ => 0) (tapes r c cap work)

theorem budget_le (r : Request) (c : ℕ) (hroot : c≤MatrixBucketDimensions.capacity r.U) :
    MatrixBucketRootStage.budget r c+1+(2*min r.U (c^10)+6)≤budget r := by
  have hD : 104000*(r.U+1)≤D r := (MatrixBatchCapacity.request_capacity r).2
  have hp := (MatrixBucketDimensions.power_budget r.U c Nat.one_le_two_pow hroot).trans hD
  have hm := Nat.min_le_left r.U (c^10)
  unfold MatrixBucketRootStage.budget budget
  omega

theorem test_run (r : Request) (c cap : ℕ) (backing : Fin 23 → List Bool)
    (hb : ∀ i,(backing i).length≤D r) (hc : 1≤c) (hroot : c≤MatrixBucketDimensions.capacity r.U) :
    ∃ work : Fin 23 → List Bool,(∀ i,(work i).length≤D r) ∧
      work 21=ZeroPadding.pad (D r) [decide (r.U≤c^10)] ∧
      ∃ actual,runFrom machine (budget r) (input r c cap backing)=some actual ∧
        actual.final.heads=(fun _ => 0) ∧
        actual.final.tapes=tapes r c (max cap (D r+1)) work ∧ actual.steps≤budget r := by
  obtain ⟨prepared,hp,ph,p0,p20,p22,p23,p24,p25,p26,pbound,ps⟩ :=
    MatrixBucketRootStage.stage_run r c cap backing hb hc hroot
  have hD : 104000*(r.U+1)≤D r := (MatrixBatchCapacity.request_capacity r).2
  have hmin : min r.U (c^10)+2≤D r := by have hm := Nat.min_le_left r.U (c^10); omega
  have hpos : 1≤D r := by omega
  have ready := MatrixBucketDimensions.Compare.compare_run r.U (c^10) (D r) hmin
  obtain ⟨checked,hcheck,ch,ct,cs⟩ := HierarchyBinary.focused_run slots slots_injective
    MatrixBucketDimensions.Compare.machine _ _ ready prepared.final.heads prepared.final.tapes
    (by intro i; rw [ph])
    (by intro i; fin_cases i; exact p22; exact p20; exact p23; exact p24)
  have joined := Composition.run_join MatrixBucketRootStage.machine last _ _ _ prepared checked hp hcheck
  have localT (i : Fin 4) : checked.final.tapes (slots i)=MatrixBucketDimensions.Compare.paddedOutput r.U (c^10) (D r) i := by
    rw [ct]
    exact install_slot slots slots_injective _ _ i
  have otherT (i : Fin 27) (hn : RecoveryFocus.pick slots i=none) : checked.final.tapes i=prepared.final.tapes i := by
    rw [ct]
    simp only [install,hn]
  have a0 := (otherT 0 (by decide)).trans p0
  have a22 := localT 0
  have a25 := (otherT 25 (by decide)).trans p25
  have a26 := (otherT 26 (by decide)).trans p26
  let work := fun i => checked.final.tapes (scratchSlots i)
  have bound : ∀ i,(work i).length≤D r := by
    intro i
    fin_cases i
    · exact (congrArg List.length (otherT 1 (by decide))).trans_le (pbound 0)
    · exact (congrArg List.length (otherT 2 (by decide))).trans_le (pbound 1)
    · exact (congrArg List.length (otherT 3 (by decide))).trans_le (pbound 2)
    · exact (congrArg List.length (otherT 4 (by decide))).trans_le (pbound 3)
    · exact (congrArg List.length (otherT 5 (by decide))).trans_le (pbound 4)
    · exact (congrArg List.length (otherT 6 (by decide))).trans_le (pbound 5)
    · exact (congrArg List.length (otherT 7 (by decide))).trans_le (pbound 6)
    · exact (congrArg List.length (otherT 8 (by decide))).trans_le (pbound 7)
    · exact (congrArg List.length (otherT 9 (by decide))).trans_le (pbound 8)
    · exact (congrArg List.length (otherT 10 (by decide))).trans_le (pbound 9)
    · exact (congrArg List.length (otherT 11 (by decide))).trans_le (pbound 10)
    · exact (congrArg List.length (otherT 12 (by decide))).trans_le (pbound 11)
    · exact (congrArg List.length (otherT 13 (by decide))).trans_le (pbound 12)
    · exact (congrArg List.length (otherT 14 (by decide))).trans_le (pbound 13)
    · exact (congrArg List.length (otherT 15 (by decide))).trans_le (pbound 14)
    · exact (congrArg List.length (otherT 16 (by decide))).trans_le (pbound 15)
    · exact (congrArg List.length (otherT 17 (by decide))).trans_le (pbound 16)
    · exact (congrArg List.length (otherT 18 (by decide))).trans_le (pbound 17)
    · exact (congrArg List.length (otherT 19 (by decide))).trans_le (pbound 18)
    · have he := (localT 1).trans p20.symm
      exact (congrArg List.length he).trans_le (pbound 19)
    · exact (congrArg List.length (otherT 21 (by decide))).trans_le (pbound 20)
    · change (checked.final.tapes (slots 2)).length≤D r
      rw [localT]
      change (ZeroPadding.pad (D r) [decide (r.U≤c^10)]).length≤D r
      simp only [ZeroPadding.pad_length,List.length_cons,List.length_nil]
      omega
    · change (checked.final.tapes (slots 3)).length≤D r
      rw [localT]
      change (List.replicate (D r) false).length≤D r
      rw [List.length_replicate]
  have complete : checked.final.tapes=tapes r c (max cap (D r+1)) work := by
    funext i
    fin_cases i
    · exact a0
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact a22
    · rfl
    · rfl
    · exact a25
    · exact a26
  have hbudget := budget_le r c hroot
  have enlarged := runFrom_moreFuel machine _ (budget r-(MatrixBucketRootStage.budget r c+1+(2*min r.U (c^10)+6)))
    _ (Composition.joinedReceipt prepared checked) joined
  rw [Nat.add_sub_of_le hbudget] at enlarged
  refine ⟨work,bound,localT 2,Composition.joinedReceipt prepared checked,enlarged,ch.trans ph,complete,?_⟩
  change prepared.steps+1+checked.steps≤budget r
  rw [cs]
  omega

end NearCubicWires.RepairOrdinary.MatrixBucketRootTest
