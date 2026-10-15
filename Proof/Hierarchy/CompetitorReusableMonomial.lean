import Proof.Hierarchy.CompetitorMonomialGlobalTerm

/-! The whole monomial-record producer executes on the retained finite
zero workspace used by the stream loop. The append prefix is untouched by
padding, and every materialized local tape fits the next physical clear. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialTarget
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorRationalDecision CompetitorMonomialProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padding (t : ℕ) (i : Fin 79) := if i.val=74 then 0 else CompetitorReusableDecision.capacity t
def paddedInput (b t : ℕ) (q : ℚ) (count denominator : ℕ) (pre : List Bool) : Fin 79 → List Bool :=
  fun i => ZeroPadding.pad (padding t i) (targetInput b t q count denominator pre i)

theorem input_support (b t : ℕ) (q : ℚ) (count denominator : ℕ) (pre : List Bool)
    (htarget : width b≤t) (hpre : pre.length≤100*(t+1)^2) (i : Fin 79) :
    (targetInput b t q count denominator pre i).length≤CompetitorReusableDecision.capacity t := by
  have hbt : b≤t := by unfold width at htarget; omega
  have hcap : CompetitorReusableDecision.capacity b≤CompetitorReusableDecision.capacity t := by
    unfold CompetitorReusableDecision.capacity
    nlinarith
  have hw : width t≤CompetitorReusableDecision.capacity t := by
    unfold width CompetitorReusableDecision.capacity
    nlinarith
  have ht : t≤CompetitorReusableDecision.capacity t := by unfold CompetitorReusableDecision.capacity; nlinarith
  have hp : pre.length≤CompetitorReusableDecision.capacity t := by unfold CompetitorReusableDecision.capacity; omega
  have hnative (j : Fin 75) : (input b t q count denominator pre j).length≤CompetitorReusableDecision.capacity t := by
    unfold input
    split
    · next hj =>
      exact (CompetitorReusableDecision.input_support b (operands q) denominator count ⟨j.val,hj⟩).trans hcap
    · split
      · simpa using hw
      · split
        · exact hp
        · simp
  refine Fin.addCases (m := 75) (n := 4) ?_ ?_ i
  · intro j
    simpa [targetInput] using hnative j
  · intro j
    simp only [targetInput,Fin.addCases_right]
    fin_cases j
    · simpa using ht
    · simp
    · simp
    · simp

theorem padded_record_run (b t : ℕ) (q : ℚ) (count denominator : ℕ) (pre : List Bool)
    (hp : positive q<2^b) (hn : negative q<2^b) (hq : q.den<2^b)
    (hc : count<2^b) (hd : denominator<2^b) (htarget : width b≤t)
    (hpre : pre.length≤100*(t+1)^2) :
    ∃ r out,runFrom machine (budget b t)
        (RecoveryCalls.restarted machine (targetHeads pre) (paddedInput b t q count denominator pre))=some r ∧
      r.steps≤budget b t ∧ r.final.tapes=out ∧
      r.final.heads=targetHeads (pre++CompetitorSumFold.termWord t (contribution q count denominator)) ∧
      out 74=pre++CompetitorSumFold.termWord t (contribution q count denominator) ∧
      (∀ i,(out i).length≤CompetitorReusableDecision.capacity t) := by
  obtain ⟨base,hr,hs,hh,ht⟩ := record_run b t q count denominator pre hp hn hq hc hd htarget
  have hsteps := hs.trans (budget_bound b t htarget)
  have hend : pre.length+base.steps+1≤CompetitorReusableDecision.capacity t := by
    unfold CompetitorReusableDecision.capacity
    have hpos : 0<(t+1)^2 := by positivity
    omega
  have hsupport := RecoveryTapeSupport.run_support machine _ _ base hr (CompetitorReusableDecision.capacity t) pre.length
    (by intro i; simp [RecoveryCalls.restarted,targetHeads]; split <;> omega)
    (by intro i; exact (input_support b t q count denominator pre htarget hpre i).trans (Nat.le_max_left _ _))
  have hbound (i : Fin 79) : (base.final.tapes i).length≤CompetitorReusableDecision.capacity t := by
    simpa only [max_eq_left hend] using hsupport i
  obtain ⟨r,hrun,hf,hstep,_⟩ := ZeroPadding.run_config machine (padding t) _ _ base hr
  refine ⟨r,r.final.tapes,hrun,hstep.trans_le hs,rfl,?_,?_,?_⟩
  · rw [hf]
    exact hh
  · simpa [hf,ZeroPadding.config,padding] using ht
  · intro i
    rw [hf]
    simp only [ZeroPadding.config,ZeroPadding.pad_length]
    exact max_le (by unfold padding; split <;> omega) (hbound i)

end NearCubicWires.RepairOrdinary.CompetitorMonomialTarget
