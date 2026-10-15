import Proof.Hierarchy.CompetitorSameBucketZeroRowNative

/-! Whole zero-grid row and its paid return to the next row's reusable
entry. Both row/column counters are actual words; final increments fit. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroBody
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Composition.machine CompetitorSameBucketZeroRowNative.machine CompetitorSameBucketZeroFinish.machine
def cfg {s : ℕ} (q : Fin s) (p m u left cap : ℕ) (out : List Bool):=
  CompetitorSameBucketZeroFinish.cfg q p m u left cap out (ZeroPadding.pad cap (frame (binary m u)))
def budget (p m u cap : ℕ):=CompetitorSameBucketZeroRow.budget p m u+1+CompetitorSameBucketZeroFinish.budget m cap

theorem body_run (p m u left cap : ℕ) (out : List Bool)
    (hp : 2*(p+1)≤cap) (hc : 4*m+3≤cap) (hu : u+u<2^m) (hl : left+1<2^m) :
    ∃ actual,runFrom machine (budget p m u cap) (cfg machine.start p m u left cap out)=some actual ∧
      actual.final.heads=(cfg machine.start p m u (left+1) cap (out++CompetitorSameBucketZeroRow.bits p m left u u)).heads ∧
      actual.final.tapes=(cfg machine.start p m u (left+1) cap (out++CompetitorSameBucketZeroRow.bits p m left u u)).tapes ∧
      actual.steps≤budget p m u cap := by
  obtain ⟨row,hr,rh,rt,rs⟩:=CompetitorSameBucketZeroRowNative.row_run p m u left cap out hp (by omega) hu
  obtain ⟨last,hlast,lh,lt,ls⟩:=CompetitorSameBucketZeroFinish.finish_run p m u left cap
    (out++CompetitorSameBucketZeroRow.bits p m left u u) (ZeroPadding.pad cap (frame (binary m (u+u))))
    (by simp [ZeroPadding.pad_length]; omega) hc hl
  have he : Composition.restart row.final CompetitorSameBucketZeroFinish.machine.start=
      CompetitorSameBucketZeroFinish.cfg CompetitorSameBucketZeroFinish.machine.start p m u left cap
        (out++CompetitorSameBucketZeroRow.bits p m left u u) (ZeroPadding.pad cap (frame (binary m (u+u)))) :=
    configuration_ext rfl rh rt
  rw [←he] at hlast
  have joined:=Composition.run_join CompetitorSameBucketZeroRowNative.machine CompetitorSameBucketZeroFinish.machine _ _ _ row last hr hlast
  refine ⟨Composition.joinedReceipt row last,joined,lh,lt,?_⟩
  change row.steps+1+last.steps≤budget p m u cap
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroBody
