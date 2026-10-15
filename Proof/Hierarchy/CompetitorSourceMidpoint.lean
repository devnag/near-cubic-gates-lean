import Proof.Hierarchy.CompetitorSourceAverage
import Proof.Hierarchy.CompetitorRationalTolerance

/-! The fixed interior rational reserve absorbs the actual outer N^-10
acceptance mass. The midpoint consumer keeps the separate estimation and
rounding errors visible until the enclosing record producer supplies them. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSourceAverage
open RepairSource RepairRepresentation SourceInterfaces PCPPRequestBoundary
open ProjectionPCPPadding CompetitorRationalGap
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem outer_error_onset {source : PointwisePCPPAlgorithm} (constants : Constants source) :
    ∃ onset : ℕ,1 ≤ onset ∧ ∀ n,onset ≤ n →
      source.soundness+1/(n : ℝ)^10 ≤ (constants.soundness : ℝ) := by
  let reserve : ℝ := constants.soundness-source.soundness
  have hreserve : 0 < reserve := sub_pos.mpr constants.lower
  obtain ⟨k,hk⟩ := exists_nat_gt (1/reserve)
  refine ⟨max 1 k,le_max_left _ _,?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans (le_max_left 1 k) hn)
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hkN : (k : ℝ) ≤ n := by exact_mod_cast (le_trans (le_max_right 1 k) hn)
  have hrec : 1/(n : ℝ) ≤ reserve := by
    have h := one_div_le_one_div_of_le (one_div_pos.mpr hreserve) (hk.le.trans hkN)
    simpa only [one_div_one_div] using h
  have hpow : 1/(n : ℝ)^10 ≤ 1/(n : ℝ) :=
    one_div_le_one_div_of_le hn0 (le_self_pow₀ hn1 (by decide : (10 : ℕ) ≠ 0))
  have hle := hpow.trans hrec
  dsimp [reserve] at hle
  linarith

theorem ordinary_no_below_midpoint {T : ℕ → ℕ} {H : OrdinaryHierarchy T}
    {degrees : PCPDegrees} (P : OrdinaryPCPResult H degrees)
    (source : PointwisePCPPAlgorithm) (constants : Constants source) :
    ∃ onset : ℕ,1 ≤ onset ∧ ∀ n,onset ≤ n → ∀ (x : BitInput n)
      (oracle : BooleanCircuit (P.pcp.nativeWidth n)),H.timedView.accepts n x=false →
      ∀ (auxiliary : BitInput (domain source (P.pcp.nativeWidth n)) →
        BitInput (source.output (PCPPSubstitution.sourceRequest source oracle
          (P.pcp.queryAddressBits x) (P.pcp.decision x (fun _=>false)))).auxiliaryBits)
        (estimate : ℝ),
      estimate ≤ satisfiedMean source (PCPPSubstitution.sourceRequest source oracle
        (P.pcp.queryAddressBits x) (P.pcp.decision x (fun _=>false))) auxiliary+
        estimationTolerance constants (zeta constants)+6*Real.sqrt (12*(zeta constants : ℝ)) →
      estimate < (midpoint constants : ℝ) := by
  obtain ⟨onset,honset,hreserve⟩ := outer_error_onset constants
  refine ⟨onset,honset,?_⟩
  intro n hn x oracle hno auxiliary estimate hestimate
  have hsound := ordinary_no_average P source x oracle (honset.trans hn) hno auxiliary
  have hbound := hreserve n hn
  apply no_branch_below_midpoint constants estimate
  linarith

theorem request_yes_above_midpoint {T : ℕ → ℕ} {H : OrdinaryHierarchy T}
    {degrees : PCPDegrees} (P : OrdinaryPCPResult H degrees)
    (source : PointwisePCPPAlgorithm) (constants : Constants source) {n : ℕ}
    (x : BitInput n) (oracle : BooleanCircuit (P.pcp.nativeWidth n))
    (hyes : ∀ randomness,P.pcp.accepts x (oracleProof oracle) randomness=true)
    (estimate : ℝ)
    (hestimate : satisfiedMean source (PCPPSubstitution.sourceRequest source oracle
      (P.pcp.queryAddressBits x) (P.pcp.decision x (fun _=>false)))
      (source.output (PCPPSubstitution.sourceRequest source oracle (P.pcp.queryAddressBits x)
        (P.pcp.decision x (fun _=>false)))).honestAuxiliary-
      estimationTolerance constants (zeta constants)-6*Real.sqrt (12*(zeta constants : ℝ)) ≤ estimate) :
    (midpoint constants : ℝ) < estimate := by
  have hcomplete := source_complete_average source (PCPPSubstitution.sourceRequest source oracle
    (P.pcp.queryAddressBits x) (P.pcp.decision x (fun _=>false))) (fun u => by
      change (request source (PCPPSubstitution.compactSubstituted oracle
        (P.pcp.queryAddressBits x) (P.pcp.decision x (fun _=>false)))).circuit.eval u=true
      rw [request_eval,outer_eval P.pcp x oracle (P.decisionIndependent n x)]
      exact hyes _)
  apply yes_branch_above_midpoint constants estimate
  have hupper := constants.upper
  linarith

end NearCubicWires.RepairOrdinary.CompetitorSourceAverage
