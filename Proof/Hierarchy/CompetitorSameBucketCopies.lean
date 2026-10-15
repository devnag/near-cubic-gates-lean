import Proof.Hierarchy.CompetitorSameBucketCopyFields

/-! The five executed scalar-field copies needed at the native all-gate
entry. Shared copy logs are reset after each call; all ambient cursors stay
at their actual previous positions. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdCopies
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open MatrixScoreBatch (Request)
open CompetitorSameBucketColdCopyFields (sourceSlot targetSlot slots copied values cfg)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := Composition.machine (CompetitorSameBucketColdCopyFields.machine 0)
  (Composition.machine (CompetitorSameBucketColdCopyFields.machine 1)
    (Composition.machine (CompetitorSameBucketColdCopyFields.machine 2)
      (Composition.machine (CompetitorSameBucketColdCopyFields.machine 3) (CompetitorSameBucketColdCopyFields.machine 4))))
def output (r : Request) (ambient : Fin 442 → List Bool) :=
  copied 4 (CompetitorSameBucketBucketBody.scalarCapacity r) (values r 4)
  (copied 3 (CompetitorSameBucketBucketBody.scalarCapacity r) (values r 3)
  (copied 2 (CompetitorSameBucketBucketBody.scalarCapacity r) (values r 2)
  (copied 1 (CompetitorSameBucketBucketBody.scalarCapacity r) (values r 1)
  (copied 0 (CompetitorSameBucketBucketBody.scalarCapacity r) (values r 0) ambient))))
def budget (r : Request) := 24*r.M+16*r.p+60

private theorem joined {a b : ℕ} (p : Machine 442 a) (q : Machine 442 b)
    (c d : ℕ) (heads : Fin 442 → ℕ) (input middle final : Fin 442 → List Bool)
    (hp : ∃ actual,runFrom p c (cfg p.start heads input)=some actual ∧
      actual.final.heads=heads ∧ actual.final.tapes=middle ∧ actual.steps≤c)
    (hq : ∃ actual,runFrom q d (cfg q.start heads middle)=some actual ∧
      actual.final.heads=heads ∧ actual.final.tapes=final ∧ actual.steps≤d) :
    ∃ actual,runFrom (Composition.machine p q) (c+1+d)
        (cfg (Composition.machine p q).start heads input)=some actual ∧
      actual.final.heads=heads ∧ actual.final.tapes=final ∧ actual.steps≤c+1+d := by
  obtain ⟨first,hfirst,fh,ft,fs⟩:=hp
  obtain ⟨last,hlast,lh,lt,ls⟩:=hq
  have he : Composition.restart first.final q.start=cfg q.start heads middle := by
    apply configuration_ext
    · rfl
    · exact fh
    · exact ft
  rw [←he] at hlast
  have h:=Composition.run_join p q c d _ first last hfirst hlast
  refine ⟨Composition.joinedReceipt first last,h,lh,lt,?_⟩
  change first.steps+1+last.steps≤c+1+d
  omega

theorem copies_run (r : Request) (heads : Fin 442 → ℕ) (ambient : Fin 442 → List Bool)
    (hh : ∀ j k,heads (slots j k)=0)
    (hs : ∀ j,ambient (sourceSlot j)=frame (values r j))
    (ht : ∀ j,ambient (targetSlot j)=List.replicate (CompetitorSameBucketBucketBody.scalarCapacity r) false)
    (h399 : ambient 399=List.replicate (CompetitorSameBucketBucketBody.scalarCapacity r) false)
    (h400 : ambient 400=List.replicate (CompetitorSameBucketBucketBody.scalarCapacity r) false) :
    ∃ actual,runFrom machine (budget r) (cfg machine.start heads ambient)=some actual ∧
      actual.final.heads=heads ∧ actual.final.tapes=output r ambient ∧ actual.steps≤budget r := by
  let cap:=CompetitorSameBucketBucketBody.scalarCapacity r
  let mid1:=copied 0 cap (values r 0) ambient
  have h0:=CompetitorSameBucketColdCopyFields.copy_run 0 cap (values r 0) heads ambient
    (CompetitorSameBucketColdCopyFields.values_fit r 0) (hh 0)
    (by simpa [copied, sourceSlot, targetSlot] using hs 0)
    (by simpa [copied, sourceSlot, targetSlot] using ht 0)
    (by simpa [copied, sourceSlot, targetSlot] using h399)
    (by simpa [copied, sourceSlot, targetSlot] using h400)
  let mid2:=copied 1 cap (values r 1) mid1
  have h1:=CompetitorSameBucketColdCopyFields.copy_run 1 cap (values r 1) heads mid1
    (CompetitorSameBucketColdCopyFields.values_fit r 1) (hh 1)
    (by simpa [mid1, copied, sourceSlot, targetSlot] using hs 1)
    (by simpa [mid1, copied, sourceSlot, targetSlot] using ht 1)
    (by simpa [mid1, copied, sourceSlot, targetSlot] using h399)
    (by simpa [mid1, copied, sourceSlot, targetSlot] using h400)
  let mid3:=copied 2 cap (values r 2) mid2
  have h2:=CompetitorSameBucketColdCopyFields.copy_run 2 cap (values r 2) heads mid2
    (CompetitorSameBucketColdCopyFields.values_fit r 2) (hh 2)
    (by simpa [mid2, mid1, copied, sourceSlot, targetSlot] using hs 2)
    (by simpa [mid2, mid1, copied, sourceSlot, targetSlot] using ht 2)
    (by simpa [mid2, mid1, copied, sourceSlot, targetSlot] using h399)
    (by simpa [mid2, mid1, copied, sourceSlot, targetSlot] using h400)
  let mid4:=copied 3 cap (values r 3) mid3
  have h3:=CompetitorSameBucketColdCopyFields.copy_run 3 cap (values r 3) heads mid3
    (CompetitorSameBucketColdCopyFields.values_fit r 3) (hh 3)
    (by simpa [mid3, mid2, mid1, copied, sourceSlot, targetSlot] using hs 3)
    (by simpa [mid3, mid2, mid1, copied, sourceSlot, targetSlot] using ht 3)
    (by simpa [mid3, mid2, mid1, copied, sourceSlot, targetSlot] using h399)
    (by simpa [mid3, mid2, mid1, copied, sourceSlot, targetSlot] using h400)
  let mid5:=copied 4 cap (values r 4) mid4
  have h4:=CompetitorSameBucketColdCopyFields.copy_run 4 cap (values r 4) heads mid4
    (CompetitorSameBucketColdCopyFields.values_fit r 4) (hh 4)
    (by simpa [mid4, mid3, mid2, mid1, copied, sourceSlot, targetSlot] using hs 4)
    (by simpa [mid4, mid3, mid2, mid1, copied, sourceSlot, targetSlot] using ht 4)
    (by simpa [mid4, mid3, mid2, mid1, copied, sourceSlot, targetSlot] using h399)
    (by simpa [mid4, mid3, mid2, mid1, copied, sourceSlot, targetSlot] using h400)
  have tail3:=joined _ _ _ _ heads mid3 mid4 mid5 h3 h4
  have tail2:=joined _ _ _ _ heads mid2 mid3 mid5 h2 tail3
  have tail1:=joined _ _ _ _ heads mid1 mid2 mid5 h1 tail2
  have all:=joined _ _ _ _ heads ambient mid1 mid5 h0 tail1
  have total : (8*(values r 0).length+8)+1+((8*(values r 1).length+8)+1+
      ((8*(values r 2).length+8)+1+((8*(values r 3).length+8)+1+(8*(values r 4).length+8))))=budget r := by
    simp [values,budget]
    omega
  rw [total] at all
  exact all

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdCopies
