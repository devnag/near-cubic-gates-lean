import Proof.Hierarchy.CompetitorSameBucketFrameCopy

/-! Exact same-bucket scalar initialization copies on the allocated442
layout. Existing global work cursors are preserved throughout each call. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdCopyFields
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sourceSlot : Fin 5 → Fin 442 := ![301,301,34,395,395]
def targetSlot : Fin 5 → Fin 442 := ![405,431,423,429,430]
def slots (j : Fin 5) : Fin 4 → Fin 442 := ![sourceSlot j,targetSlot j,399,400]
theorem slots_injective (j : Fin 5) : Function.Injective (slots j) := by fin_cases j <;> decide
noncomputable def machine (j : Fin 5) := RecoveryFocus.machine (slots j) RecoveryRootRound.copyMachine
def copied (j : Fin 5) (cap : ℕ) (bits : List Bool) (ambient : Fin 442 → List Bool) :=
  Function.update ambient (targetSlot j) (ZeroPadding.pad cap (frame bits))
def cfg {s : ℕ} (q : Fin s) (heads : Fin 442 → ℕ) (tapes : Fin 442 → List Bool) : Configuration 442 s := ⟨q,heads,tapes⟩

theorem copy_run (j : Fin 5) (cap : ℕ) (bits : List Bool) (heads : Fin 442 → ℕ) (ambient : Fin 442 → List Bool)
    (hc : 4*bits.length+3≤cap) (hh : ∀ k,heads (slots j k)=0)
    (hs : ambient (sourceSlot j)=frame bits) (ht : ambient (targetSlot j)=List.replicate cap false)
    (h399 : ambient 399=List.replicate cap false) (h400 : ambient 400=List.replicate cap false) :
    ∃ actual,runFrom (machine j) (8*bits.length+8) (cfg (machine j).start heads ambient)=some actual ∧
      actual.final.heads=heads ∧ actual.final.tapes=copied j cap bits ambient ∧ actual.steps≤8*bits.length+8 := by
  obtain ⟨base,hb,bt,bh,bs⟩:=CompetitorSameBucketColdFrameCopy.copy_ready bits cap hc
  have ready : ClockJoin.ReadyRun RecoveryRootRound.copyMachine (8*bits.length+8)
      (CompetitorSameBucketColdFrameCopy.input bits cap) (CompetitorSameBucketColdFrameCopy.output bits cap) :=
    ⟨base,hb,bt,bh,bs.le⟩
  obtain ⟨actual,ha,ah,atapes,ast⟩:=CompetitorReusableDecision.bounded_focused_run (slots j) (slots_injective j)
    _ _ _ ready heads ambient hh (by intro k; fin_cases k; exact hs; exact ht; exact h399; exact h400)
  refine ⟨actual,ha,ah,?_,ast⟩
  rw [atapes]
  funext i
  by_cases htarget : i=targetSlot j
  · subst i
    rw [copied,Function.update_self]
    exact install_slot (slots j) (slots_injective j) _ _ 1
  rw [copied,Function.update_of_ne htarget]
  by_cases hsource : i=sourceSlot j
  · subst i
    exact (install_slot (slots j) (slots_injective j) _ _ 0).trans hs.symm
  by_cases hc1 : i=399
  · subst i
    exact (install_slot (slots j) (slots_injective j) _ _ 2).trans h399.symm
  by_cases hc2 : i=400
  · subst i
    exact (install_slot (slots j) (slots_injective j) _ _ 3).trans h400.symm
  apply install_other
  intro k hk
  fin_cases k
  · exact hsource hk.symm
  · exact htarget hk.symm
  · exact hc1 hk.symm
  · exact hc2 hk.symm

theorem copied_other (j : Fin 5) (cap : ℕ) (bits : List Bool) (ambient : Fin 442 → List Bool)
    (i : Fin 442) (hi : i≠targetSlot j) : copied j cap bits ambient i=ambient i := Function.update_of_ne hi _ _

def values (r : Request) : Fin 5 → List Bool :=
  ![SignedSortKey.binary r.M 0,SignedSortKey.binary r.M 0,SignedSortKey.binary r.M r.U,
    List.replicate (r.p+1) false,List.replicate (r.p+1) false]

theorem values_fit (r : Request) (j : Fin 5) :
    4*(values r j).length+3≤CompetitorSameBucketBucketBody.scalarCapacity r := by
  have hc:=(CompetitorSameBucketBucketBody.scalar_capacity_fits r).1
  have hm : r.M≤MatrixBatchBucketEndpoints.H r := by unfold MatrixBatchBucketEndpoints.H; omega
  have hp : r.p≤MatrixBatchBucketEndpoints.H r := by
    unfold MatrixBatchBucketEndpoints.H MatrixScoreBatch.Request.S
    omega
  fin_cases j <;> simp [values] <;> omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdCopyFields
