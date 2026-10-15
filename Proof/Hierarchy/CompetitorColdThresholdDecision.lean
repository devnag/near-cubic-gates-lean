import Proof.Hierarchy.CompetitorThresholdFold

/-! Whole ordinary cold scalar-stream decision. The true rational sum is
computed on tapes, the fixed threshold is printed, and the exact rational
comparison produces the final bit. No precomputed estimate or extra prefix
overflow condition is supplied at the uniform-width theorem. -/
namespace NearCubicWires.RepairOrdinary.CompetitorThresholdCold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorSumFold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine (lower : Bool) (k : ℕ) (q : ℚ) :=
  Composition.machine foldProgram (CompetitorThresholdAmbient.machine lower k q)
def budget (b k n : ℕ) := CompetitorSumEntry.budget b n+1+CompetitorThresholdAmbient.budget b k
def passes (lower : Bool) (q : ℚ) (xs : List CompetitorValidity.Estimate) : Prop :=
  if lower then q≤(xs.map CompetitorValidity.Estimate.value).sum else (xs.map CompetitorValidity.Estimate.value).sum≤q

theorem cold_decision_run (lower : Bool) (b k : ℕ) (q : ℚ) (xs : List CompetitorValidity.Estimate)
    (hb : 1≤b) (hv : CompetitorSumWidth.Trace b CompetitorSumWidth.zero xs)
    (hq : 0≤q) (hk : k≤b)
    (hp : CompetitorThresholdDecision.numerator q<2^k) (hd : q.den<2^k) :
    ∃ r,run (machine lower k q) (budget b k xs.length) (input b xs)=some r ∧
      r.steps≤budget b k xs.length ∧ r.final.heads 65=0 ∧
      (readTapeBit (r.final.tapes 65) 0=true ↔ passes lower q xs) := by
  obtain ⟨first,hfirst,hfs,hstore,hheads,hfreshHeads,hfresh,hvalue⟩ := fold_run b xs hb hv
  obtain ⟨last,hlast,hls,hlh,hflag⟩ := CompetitorThresholdAmbient.tail_run lower b k (words b xs).length q
    (folded CompetitorSumWidth.zero xs) (words b xs) first.final.heads first.final.tapes
    hstore hheads hfreshHeads hfresh (folded_valid b _ xs hv) hq hk hp hd
  have he : Composition.restart first.final (CompetitorThresholdAmbient.machine lower k q).start=
      RecoveryCalls.restarted (CompetitorThresholdAmbient.machine lower k q) first.final.heads first.final.tapes := rfl
  have hlast' : runFrom (CompetitorThresholdAmbient.machine lower k q) (CompetitorThresholdAmbient.budget b k)
      (Composition.restart first.final (CompetitorThresholdAmbient.machine lower k q).start)=some last := by
    rw [he]
    exact hlast
  have hall := Composition.run_join foldProgram (CompetitorThresholdAmbient.machine lower k q) _ _ _ first last hfirst hlast'
  refine ⟨Composition.joinedReceipt first last,hall,?_,?_,?_⟩
  · change first.steps+1+last.steps≤budget b k xs.length
    unfold budget
    omega
  · change last.final.heads 65=0
    rw [hlh]
    exact hheads 65
  · change readTapeBit (last.final.tapes 65) 0=true ↔ passes lower q xs
    have heValue : CompetitorThresholdDecision.estimate (folded CompetitorSumWidth.zero xs).positive
        (folded CompetitorSumWidth.zero xs).negative (folded CompetitorSumWidth.zero xs).denominator=
        (xs.map CompetitorValidity.Estimate.value).sum := hvalue
    simpa only [CompetitorThresholdDecision.passes,passes,heValue] using hflag

theorem uniform_cold_decision_run (lower : Bool) (k : ℕ) (q : ℚ) (xs : List CompetitorValidity.Estimate)
    (hv : ∀ a∈xs,a.Valid k) (hq : 0≤q)
    (hp : CompetitorThresholdDecision.numerator q<2^k) (hd : q.den<2^k) :
    ∃ r,run (machine lower k q) (budget (CompetitorSumWidth.width xs.length k) k xs.length)
        (input (CompetitorSumWidth.width xs.length k) xs)=some r ∧
      r.steps≤budget (CompetitorSumWidth.width xs.length k) k xs.length ∧ r.final.heads 65=0 ∧
      (readTapeBit (r.final.tapes 65) 0=true ↔ passes lower q xs) := by
  exact cold_decision_run lower (CompetitorSumWidth.width xs.length k) k q xs
    (by unfold CompetitorSumWidth.width; nlinarith) (CompetitorSumWidth.uniform_trace k xs hv) hq
    (by unfold CompetitorSumWidth.width; nlinarith) hp hd

theorem budget_bound (b k n : ℕ) (hk : k≤b) :
    budget b k n≤25000*(n+1)*(b+1)^2 := by
  unfold budget CompetitorSumEntry.budget CompetitorThresholdAmbient.budget
    CompetitorThresholdConstants.budget loopBudget bodyBudget CompetitorReusableDecision.capacity
  have hsq : b+1≤(b+1)^2 := by nlinarith
  have hprod : n≤n*(b+1)^2 := by nlinarith
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorThresholdCold
