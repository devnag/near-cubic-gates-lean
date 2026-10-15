import Proof.Hierarchy.CompetitorMonomialNative

/-! Enclosing reusable coefficient/count record execution. Every iteration
physically clears local scratch, copies runtime widths, reads six fields,
multiplies and widens the exact signed contribution, and appends its term. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision CompetitorMonomialProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def bodyProgram := Composition.machine prepareProgram nativeProgram
def bodyBudget (t : ℕ) := 12000*(t+1)^2

theorem body_run (b t : ℕ) (q : ℚ) (count denominator : ℕ) (pre suffix output : List Bool)
    (ambient : Fin 88 → List Bool)
    (h : Store b t (pre++recordWord b q count denominator++suffix) output ambient)
    (hp : positive q<2^b) (hn : negative q<2^b) (hq : q.den<2^b)
    (hc : count<2^b) (hd : denominator<2^b) (htarget : width b≤t)
    (hout : output.length≤100*(t+1)^2) :
    ∃ r,runFrom bodyProgram (bodyBudget t) (cfg output.length bodyProgram.start pre.length ambient)=some r ∧
      r.steps≤bodyBudget t ∧
      r.final.heads=heads (output++CompetitorSumFold.termWord t (contribution q count denominator)).length
        (pre.length+(recordWord b q count denominator).length) ∧
      Store b t (pre++recordWord b q count denominator++suffix)
        (output++CompetitorSumFold.termWord t (contribution q count denominator)) r.final.tapes := by
  have hbt : b≤t := by unfold width at htarget; omega
  obtain ⟨prep,hprep,hps,hph,hpt⟩ := prepare_run b t q count denominator pre suffix output ambient h hbt
  obtain ⟨last,hlast,hls,hlh,hlt⟩ := native_run b t (pre.length+(recordWord b q count denominator).length)
    q count denominator _ output ambient h hp hn hq hc hd htarget hout
  have he : Composition.restart prep.final nativeProgram.start=
      cfg output.length nativeProgram.start (pre.length+(recordWord b q count denominator).length)
        (prepared b t q count denominator ambient) := by
    apply configuration_ext
    · rfl
    · exact hph
    · exact hpt
  have hl' : runFrom nativeProgram (CompetitorMonomialTarget.budget b t)
      (Composition.restart prep.final nativeProgram.start)=some last := by rw [he]; exact hlast
  have hall := Composition.run_join prepareProgram nativeProgram _ _ _ prep last hprep hl'
  have hbound := CompetitorMonomialTarget.budget_bound b t htarget
  have hcost : prepareBudget b t+1+CompetitorMonomialTarget.budget b t≤bodyBudget t := by
    simp [prepareBudget,widthPrepareBudget,widthCost,allWidths,widths,width,capacity,bodyBudget]
    nlinarith
  let r := Composition.joinedReceipt prep last
  have hmore := runFrom_moreFuel bodyProgram _
    (bodyBudget t-(prepareBudget b t+1+CompetitorMonomialTarget.budget b t)) _ r hall
  rw [Nat.add_sub_of_le hcost] at hmore
  refine ⟨r,hmore,?_,hlh,hlt⟩
  change prep.steps+1+last.steps≤bodyBudget t
  omega

structure Entry where
  coefficient : ℚ
  count : ℕ
  denominator : ℕ

def Entry.estimate (a : Entry) := contribution a.coefficient a.count a.denominator
structure Entry.Valid (b : ℕ) (a : Entry) : Prop where
  positive : positive a.coefficient<2^b
  negative : negative a.coefficient<2^b
  coefficientDenominator : a.coefficient.den<2^b
  count : a.count<2^b
  denominator : a.denominator<2^b
  denominatorPositive : 0<a.denominator

theorem Entry.valid_estimate (b : ℕ) (a : Entry) (h : a.Valid b) : a.estimate.Valid (width b) :=
  CompetitorMonomialTarget.contribution_valid b a.coefficient a.count a.denominator
    h.positive h.negative h.coefficientDenominator h.count h.denominator h.denominatorPositive

theorem Entry.estimate_value (a : Entry) : a.estimate.value=a.coefficient*((a.count : ℚ)/a.denominator) :=
  contribution_value a.coefficient a.count a.denominator

end NearCubicWires.RepairOrdinary.CompetitorMonomialStream
