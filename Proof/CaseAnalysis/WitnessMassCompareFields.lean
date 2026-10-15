import Proof.CaseAnalysis.WitnessMassCheck

/-! Retained operands and bounded native scratch of the same exact mass
comparison, needed to reuse its accumulator bank for the next sum. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassCompareFields
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey
open CompetitorRationalDecision CompetitorReusableDecision
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem fields_run (B : ℕ) (a : Estimate) (q : ℚ) (ha : a.Valid B) (hq : 0≤q)
    (hp : CompetitorThresholdDecision.numerator q<2^B) (hd : q.den<2^B) : ∃ output,
    ClockJoin.ReadyRun machine (2000*(B+1)^2)
      (CompetitorMixedThreshold.input false B a.positive a.negative a.denominator q
        (CompetitorThresholdAmbient.pads false B)) output ∧
      (∀ i,(output i).length ≤ capacity B) ∧
      (∀ j : Fin 7,output (CompetitorRationalProducts.shared j)=
        CompetitorMixedThreshold.input false B a.positive a.negative a.denominator q
          (CompetitorThresholdAmbient.pads false B) (CompetitorRationalProducts.shared j)) ∧
      (readTapeBit (output 65) 0=true ↔ a.value≤q):=by
  let nums:=CompetitorThresholdDecision.numbers false a.positive a.negative q
  have hn:∀ i,nums i<2^B:=by
    intro i;fin_cases i
    · exact hp
    · exact Nat.two_pow_pos _
    · exact ha.positive
    · exact ha.negative
  obtain ⟨out,⟨base,hr,ht,hh,hs⟩,hshared,hflag⟩:=rational_decision_run B nums q.den a.denominator
    hn hd ha.denominator q.pos ha.denominatorPositive
  have hsupport:=RecoveryTapeSupport.run_support machine _ _ base hr (capacity B) 0
    (by intro i;exact Nat.zero_le _) (by
      intro i;exact (input_support B nums q.den a.denominator i).trans (Nat.le_max_left _ _))
  have hbound (i : Fin 67) : (base.final.tapes i).length ≤ capacity B:=by
    have hm:base.steps+1 ≤ capacity B:=by
      have hpos:0<(B+1)^2:=by positivity
      unfold capacity
      omega
    simpa only [Nat.zero_add,max_eq_left hm] using hsupport i
  obtain ⟨r,hrun,rf,rt,_⟩:=ZeroPadding.run_config machine
    (CompetitorThresholdAmbient.pads false B) _ _ base hr
  refine ⟨r.final.tapes,⟨r,hrun,rfl,?_,rt.trans_le hs⟩,?_,?_,?_⟩
  · intro i;rw [rf];exact hh i
  · intro i;rw [rf]
    simp only [ZeroPadding.config,ZeroPadding.pad_length]
    exact max_le (by unfold CompetitorThresholdAmbient.pads;split <;> omega) (hbound i)
  · intro j
    rw [rf]
    change ZeroPadding.pad _ (base.final.tapes (CompetitorRationalProducts.shared j))=_
    rw [ht,hshared]
    rfl
  · rw [rf]
    simp only [ZeroPadding.config,ZeroPadding.read_pad,ht]
    change readTapeBit (out 65) 0=true ↔
      a.value ≤ ((CompetitorThresholdDecision.numerator q : ℚ)-0)/q.den at hflag
    simpa only [sub_zero,CompetitorThresholdDecision.threshold_fraction q hq] using hflag

end NearCubicWires.RepairOrdinary.CloseoutWitness.MassCompareFields
