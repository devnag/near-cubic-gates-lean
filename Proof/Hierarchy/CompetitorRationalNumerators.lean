import Proof.Hierarchy.CompetitorMonomialProducts

/-! Expose the two actual numerator tapes of the accepted rational decision
machine. Swapping the second sign pair makes these its exact rational-addition
numerators. This is an endpoint of the existing paid execution, not a new
unaccounted arithmetic routine. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRationalNumerators
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalProducts CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem numerators_run (b : ℕ) (nums : Fin 4 → ℕ) (d e : ℕ)
    (hn : ∀ i,nums i<2^b) (hd : d<2^b) (he : e<2^b) :
    ∃ out,ClockJoin.ReadyRun machine (2000*(b+1)^2) (input (width b) b nums d e) out ∧
      (∀ j : Fin 7,out (shared j)=input (width b) b nums d e (shared j)) ∧
      out 63=frame (binary (width b) (nums 0*e+nums 3*d)) ∧
      out 64=frame (binary (width b) (nums 1*e+nums 2*d)) := by
  obtain ⟨middle,hm,hstore⟩ := products_run b nums d e hn hd he
  have hleft := sum_fit b (nums 0) (nums 3) d e (hn 0) (hn 3) hd he
  have hright := sum_fit b (nums 1) (nums 2) d e (hn 1) (hn 2) hd he
  obtain ⟨r,hr,ht,hh,hs⟩ := CompetitorSignedDecision.signed_decision_run (width b)
    (nums 0*e) (nums 1*e) (nums 2*d) (nums 3*d) hleft hright
  let localOut := CompetitorSignedDecision.output (width b)
    (nums 0*e) (nums 1*e) (nums 2*d) (nums 3*d)
  have ready : ClockJoin.ReadyRun CompetitorSignedDecision.machine (12*width b+15)
      (CompetitorSignedDecision.input (width b) (nums 0*e) (nums 1*e) (nums 2*d) (nums 3*d)) localOut :=
    ⟨r,hr,ht,hh,hs.le⟩
  have hf := bounded_focus decisionSlots (by decide) _ _ _ ready middle
    (decision_input b nums d e middle hstore)
  let out := install decisionSlots middle localOut
  have hall : ClockJoin.ReadyRun machine (totalCost b) (input (width b) b nums d e) out :=
    ClockJoin.join productsProgram decisionProgram _ _ _ middle out hm hf
  refine ⟨out,ClockJoin.enlarge machine _ _ _ out hall (totalCost_bound b),?_,?_,?_⟩
  · intro j
    have hother : ∀ k,decisionSlots k≠shared j := by
      intro k heq
      have hv := congrArg Fin.val heq
      fin_cases k <;> simp [decisionSlots,shared] at hv <;> omega
    exact (install_other decisionSlots middle localOut (shared j) hother).trans (hstore.shared j)
  · exact install_slot decisionSlots (by decide) middle localOut 4
  · exact install_slot decisionSlots (by decide) middle localOut 5

def add (a c : CompetitorValidity.Estimate) : CompetitorValidity.Estimate :=
  ⟨a.positive*c.denominator+c.positive*a.denominator,
   a.negative*c.denominator+c.negative*a.denominator,
   a.denominator*c.denominator⟩
def operands (a c : CompetitorValidity.Estimate) : Fin 4 → ℕ :=
  ![a.positive,a.negative,c.negative,c.positive]

theorem add_value (a c : CompetitorValidity.Estimate)
    (ha : 0<a.denominator) (hc : 0<c.denominator) :
    (add a c).value=a.value+c.value := by
  have ha' : (a.denominator : ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt ha
  have hc' : (c.denominator : ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt hc
  simp only [add,CompetitorValidity.Estimate.value,Nat.cast_add,Nat.cast_mul]
  field_simp
  ring

end NearCubicWires.RepairOrdinary.CompetitorRationalNumerators
