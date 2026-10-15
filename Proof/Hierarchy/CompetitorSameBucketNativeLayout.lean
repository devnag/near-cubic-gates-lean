import Proof.Hierarchy.CompetitorSameBucketInitialized

/-! Fixed native gate layout and the one paid transition positioning its
six existing sentinels. No tape contents are installed by this transition. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdNativeLayout
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open MatrixScoreBatch (Request)
open MatrixBatchBucketEndpoints (H)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 56) : Fin 442 :=
  if h : j.val<34 then ⟨398+j.val,by omega⟩ else
    ![2,432,358,436,370,437,433,218,306,438,434,380,132,441,376,439,224,164,340,440,435,91]
      ⟨j.val-34,by omega⟩
theorem slots_injective : Function.Injective slots := by decide

def advances (i : Fin 442) : Prop := i=370 ∨ i=218 ∨ i=380 ∨ i=376 ∨ i=224 ∨ i=91
instance (i : Fin 442) : Decidable (advances i) := inferInstanceAs (Decidable (i=370 ∨ i=218 ∨ i=380 ∨ i=376 ∨ i=224 ∨ i=91))
def advance : Machine 442 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q => q.val==1
  rule:=fun q _ => if q.val=0 then some ⟨1,fun _ => none,fun i => if advances i then .right else .stay⟩ else none
def advanced {s : ℕ} (c : Configuration 442 s) : Configuration 442 2 :=
  ⟨1,fun i => if advances i then c.heads i+1 else c.heads i,c.tapes⟩
theorem advance_run {s : ℕ} (c : Configuration 442 s) : ∃ actual,
    runFrom advance 1 (Composition.restart c advance.start)=some actual ∧ actual.final=advanced c ∧ actual.steps=1 := by
  have h : step advance (Composition.restart c advance.start)=some (advanced c) := by
    simp only [step,advance,Composition.restart]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; by_cases hi : advances i <;> simp [applyAction,advanced,hi,HeadMove.apply]
    · rfl
  exact (Timed.single (by rfl) h).run (by rfl)

def ambient (r : Request) : Fin 41 → List Bool := fun i =>
  if i=7 ∨ i=33 then ZeroPadding.pad (CompetitorSameBucketBucketBody.scalarCapacity r) (frame (binary r.M 0))
  else if i=25 then ZeroPadding.pad (CompetitorSameBucketBucketBody.scalarCapacity r) (frame (binary r.M r.U))
  else if i=31 ∨ i=32 then ZeroPadding.pad (CompetitorSameBucketBucketBody.scalarCapacity r) (frame (List.replicate (r.p+1) false))
  else if i=34 then []
  else if i=36 then List.replicate (CompetitorSameBucketBucketBody.scalarCapacity r) true
  else if i=37 then List.replicate (CompetitorSameBucketBucketBody.scalarCapacity r+1) false
  else if i=38 then UnaryTemplate.tape (4*H r+1)
  else if i=39 then List.replicate (MatrixScoreReusableRanks.D r) false
  else List.replicate (CompetitorSameBucketBucketBody.scalarCapacity r) false
noncomputable def entry (r : Request) := CompetitorSameBucketGateNative.cfg r
  (CompetitorSameBucketBucketBody.scalarCapacity r) 0 0 0 [] (ambient r) (List.replicate (MatrixScoreReusableRanks.D r) false)

theorem initial_state (r : Request) : CompetitorSameBucketCandidate.State r
    (CompetitorSameBucketBucketBody.scalarCapacity r) 0 none (List.replicate (MatrixScoreReusableRanks.D r) false) [] (ambient r) := by
  have hc:=(CompetitorSameBucketBucketBody.scalar_capacity_fits r).1
  constructor
  · constructor
    · simp [ambient]
    · simp [ambient]
    · intro i; fin_cases i <;> simp [ambient,CompetitorSameBucketCandidate.workSlots]
  · intro i
    fin_cases i
    · change List.replicate (CompetitorSameBucketBucketBody.scalarCapacity r) false=
        ZeroPadding.pad (CompetitorSameBucketBucketBody.scalarCapacity r) (List.replicate (4*H r+1) false)
      rw [Rewind.Workspace.pad_zeros,max_eq_left (by omega)]
    · rfl
    · rfl
    · simp [ambient,CompetitorSameBucketCandidate.fixedSlots,CompetitorSameBucketCandidate.fixed,
        MatrixScoreBatch.signMagnitude,RankCarrier.binary_zero,List.replicate_succ]
    · rfl
    · rfl
    · rfl
  · rfl
  · rfl

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdNativeLayout
