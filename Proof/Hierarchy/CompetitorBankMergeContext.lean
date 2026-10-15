import Proof.Hierarchy.CompetitorBankMergeDock

/-! Literal native TableContext is restored with pointwise natural P/N sums.
The same-bucket producer and final width proof belong to the enclosing
caller; no signed congruence or full natural count is silently assumed. -/
namespace NearCubicWires.RepairOrdinary.CompetitorBankMergeDock
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorBankMerge CompetitorPlaneTable
open CompetitorPlaneStream (Cell oldWords)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def stateAdd {n : ℕ} (a b : State n) : State n :=
  ⟨fun i => a.positive i+b.positive i,fun i => a.negative i+b.negative i⟩
def paired {n : ℕ} (a b : State n) : List Pair :=
  List.ofFn (fun i => (cell (fun _ => 0) a i,cell (fun _ => 0) b i))

@[simp] theorem paired_length {n : ℕ} (a b : State n) : (paired a b).length=n := by simp [paired]
theorem paired_left {n : ℕ} (w : ℕ) (a b : State n) : leftWords w (paired a b)=oldWords w (canonical a) := by
  simp [leftWords,paired,canonical,cells,Function.comp_def]
theorem paired_right {n : ℕ} (w : ℕ) (a b : State n) : rightWords w (paired a b)=oldWords w (canonical b) := by
  simp [rightWords,paired,canonical,cells,Function.comp_def]
theorem paired_merged {n : ℕ} (w : ℕ) (a b : State n) : mergedWords w (paired a b)=oldWords w (canonical (stateAdd a b)) := by
  simp only [mergedWords,mergedCells,paired,List.map_ofFn,canonical,cells]
  rfl

theorem aligned_run (w pos : ℕ) (xs ys : List Cell) (ambient : Fin 35 → List Bool)
    (hlen : xs.length=ys.length)
    (hw : ambient 9=ZeroPadding.pad (capacity w xs.length) (List.replicate w true))
    (hn : ambient 27=ZeroPadding.pad (capacity w xs.length) (RepairSource.VerifierDecoding.CompareMachine.word xs.length))
    (hsource : ambient 19=ZeroPadding.pad (capacity w xs.length) (oldWords w xs))
    (hd : ambient 30=List.replicate (capacity w xs.length) true)
    (hreset : ambient 31=List.replicate (capacity w xs.length+1) false)
    (hv : ∀ a∈xs.zip ys,Valid w a.1 a.2) :
    ∃ r,runFrom machine (budget w xs.length)
      (RecoveryCalls.restarted machine (heads pos) (input ambient (oldWords w ys)))=some r ∧
      r.steps≤500000*(xs.length+1)*(w+1)^2 ∧ r.final.heads=heads pos ∧
      r.final.tapes 19=ZeroPadding.pad (capacity w xs.length) (oldWords w (mergedCells (xs.zip ys))) ∧
      r.final.tapes 35=oldWords w ys ∧
      (∀ i : Fin 35,i≠19 → r.final.tapes (i.castAdd 52)=ambient i) := by
  have hl : leftWords w (xs.zip ys)=oldWords w xs := by
    unfold leftWords
    rw [List.map_fst_zip hlen.le]
  have hr : rightWords w (xs.zip ys)=oldWords w ys := by
    unfold rightWords
    rw [List.map_snd_zip hlen.ge]
  have hc : (xs.zip ys).length=xs.length := by simp [hlen]
  obtain ⟨r,hrun,hs,hh,h19,h35,hkeep⟩ := dock_run w pos (xs.zip ys) ambient
    (by simpa only [hc] using hw) (by simpa only [hc] using hn)
    (by simpa only [hc,hl] using hsource) (by simpa only [hc] using hd)
    (by simpa only [hc] using hreset) hv
  rw [hc,hr] at hrun
  rw [hc] at hs h19
  rw [hr] at h35
  exact ⟨r,hrun,hs.trans (budget_bound w xs.length),hh,h19,h35,hkeep⟩

theorem context_run {n : ℕ} (b w pos : ℕ) (cross same : State n) (ambient : Fin 35 → List Bool)
    (hcontext : TableContext b w cross (fun i : Fin 34 => ambient (i.castAdd 1)))
    (hfit : ∀ i,cross.positive i+same.positive i<2^w ∧ cross.negative i+same.negative i<2^w) :
    ∃ r,runFrom machine (budget w n)
      (RecoveryCalls.restarted machine (heads pos) (input ambient (oldWords w (canonical same))))=some r ∧
      r.steps≤500000*(n+1)*(w+1)^2 ∧ r.final.heads=heads pos ∧
      TableContext b w (stateAdd cross same) (fun i : Fin 34 => r.final.tapes (i.castAdd 53)) ∧
      r.final.tapes 19=ZeroPadding.pad (capacity w n) (oldWords w (canonical (stateAdd cross same))) ∧
      r.final.tapes 35=oldWords w (canonical same) ∧
      (∀ i : Fin 35,i≠19 → r.final.tapes (i.castAdd 52)=ambient i) := by
  have hv : ∀ a∈paired cross same,Valid w a.1 a.2 := by
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact hfit i
  obtain ⟨r,hr,hs,hh,h19,h35,hkeep⟩ := dock_run w pos (paired cross same) ambient
    (by simpa [capacity,canonical,cells_length] using hcontext.width)
    (by simpa [capacity,canonical,cells_length] using hcontext.count)
    (by rw [paired_left]; simpa [capacity,canonical,cells_length] using hcontext.old)
    (by simpa [capacity,canonical,cells_length] using hcontext.driver)
    (by simpa [capacity,canonical,cells_length] using hcontext.reset) hv
  rw [paired_length,paired_right] at hr
  rw [paired_length] at hs
  rw [paired_length,paired_merged] at h19
  rw [paired_right] at h35
  refine ⟨r,hr,hs.trans (budget_bound w n),hh,?_,h19,h35,hkeep⟩
  constructor
  · simpa [capacity,canonical,cells_length] using h19
  · exact (hkeep 9 (by decide)).trans (by simpa [canonical,cells_length] using hcontext.width)
  · exact (hkeep 20 (by decide)).trans (by simpa [canonical,cells_length] using hcontext.nativeWidth)
  · exact (hkeep 21 (by decide)).trans (by simpa [canonical,cells_length] using hcontext.erase)
  · exact (hkeep 27 (by decide)).trans (by simpa [canonical,cells_length] using hcontext.count)
  · exact (hkeep 33 (by decide)).trans (by
      simpa [CompetitorPlanePaddedEntry.count_length,canonical,cells_length] using hcontext.byteCount)
  · exact (hkeep 30 (by decide)).trans (by simpa [canonical,cells_length] using hcontext.driver)
  · exact (hkeep 31 (by decide)).trans (by simpa [canonical,cells_length] using hcontext.reset)
  · intro i
    by_cases hi : i=19
    · subst i
      change (r.final.tapes 19).length≤_
      rw [h19,ZeroPadding.pad_length]
      simp only [canonical,cells_length,CompetitorPlanePaddedEntry.old_length]
      exact max_le le_rfl (CompetitorPlanePaddedEntry.capacity_bounds w n).2.1
    · have hi' : (i.castAdd 5 : Fin 35)≠19 := fun h => hi (Fin.ext (congrArg (fun j : Fin 35 => j.val) h))
      change (r.final.tapes ((i.castAdd 5).castAdd 52)).length≤_
      rw [hkeep _ hi']
      simpa [canonical,cells_length,CompetitorPlanePacketPass.localTape,Fin.castAdd] using hcontext.support i

end NearCubicWires.RepairOrdinary.CompetitorBankMergeDock
