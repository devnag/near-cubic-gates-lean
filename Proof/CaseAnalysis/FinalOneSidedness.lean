import Proof.CaseAnalysis.WitnessSoundness
import Proof.CaseAnalysis.Language
import Proof.Assembly.SelectedRecoveryIntegration

/-! Paper C.10 one-sidedness, at the consumer.

On a hierarchy NO word the paper's argument is: outer soundness bounds the
substituted circuit's acceptance, pointwise PCPP soundness bounds every rounded
Boolean proof by `s_p`, validity moves the mean by at most `6*sqrt(12*zeta)`,
and estimation moves it by at most `(c_p - s_p)/20`; the result is strictly
below `theta_acc`. All of that is already discharged by the accepted
`CloseoutWitness.Soundness.below`.

This module performs the remaining step: it turns `below` into exactly the
`oneSided` premise that `CloseoutLanguage.hardness_pair` consumes, given only
that the machine's acceptance predicate exposes its three estimates together
with their accuracy. After this, the `sound` field of a closure record is
reduced to the accuracy facts and a length guard -- no further soundness
mathematics is required anywhere. -/
namespace NearCubicWires.RepairSource.CloseoutFinal

open RepairOrdinary RepairOrdinary.CloseoutWitness CompetitorRationalGap
open CompetitorSourceAverage AggregateSemanticStage SelectedRecoveryIntegration
open CloseoutLanguage

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2)))

/-- The selected source request at one input and one guessed oracle. -/
def req {n : Nat} (x : BitInput n)
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)) :=
  PCPPSubstitution.sourceRequest (selectedPCPP sources) oracle
    ((outer sources k clock).result.pcp.queryAddressBits x)
    ((outer sources k clock).result.pcp.decision x (fun _ => false))

/-- The selected PCPP at that request. -/
def pcppAt {n : Nat} (x : BitInput n)
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)) :=
  (selectedPCPP sources).output (req sources k clock x oracle)

/-- What the acceptance predicate must expose on every accepted input: the
guessed oracle and real proof family, the three estimates, the paper's three
threshold tests, and the accuracy of each estimate. Nothing here mentions a
tape; these are the same quantities `ordinary_estimate_below` consumes. -/
def Exposes (constants : Constants (selectedPCPP sources))
    (meaning : (n : Nat) → BitInput n → List Bool → Prop) : Prop :=
  ∀ n (x : BitInput n) (bits : List Bool), meaning n x bits →
    Soundness.cutoff constants ≤ n ∧
    ∃ oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n),
    ∃ value : BitInput (req sources k clock x oracle).arity →
      Fin ((pcppAt sources k clock x oracle).systematicBits
        + (pcppAt sources k clock x oracle).auxiliaryBits) → ℝ,
    ∃ penalty moment clause : ℝ,
      penalty ≤ 2*(zeta constants : ℝ) ∧
      moment ≤ 1+(zeta constants : ℝ) ∧
      (midpoint constants : ℝ) ≤ clause ∧
      |penalty - aggregateClausePenaltyMean (pcppAt sources k clock x oracle) value/2|
        ≤ (estimationTolerance constants (zeta constants) : ℝ) ∧
      |moment - leftSecondMoment (pcppAt sources k clock x oracle) value|
        ≤ (estimationTolerance constants (zeta constants) : ℝ) ∧
      |clause - aggregateClauseMean (pcppAt sources k clock x oracle) value|
        ≤ (estimationTolerance constants (zeta constants) : ℝ)

/-- C.10 one-sidedness for EVERY length, in exactly the form `hardness_pair`
takes. The machine never tests the semantic `[0,1]` condition; only Booleanity
and second moments are used, as the paper requires. -/
theorem sound_of_exposes (constants : Constants (selectedPCPP sources))
    (meaning : (n : Nat) → BitInput n → List Bool → Prop)
    (h : Exposes sources k clock constants meaning) :
    ∀ n (x : BitInput n) (bits : List Bool), meaning n x bits →
      (sources.hierarchy (fun n => n^(k+2)) clock).hierarchy.timedView.accepts n x = true := by
  intro n x bits hm
  by_contra hno
  obtain ⟨hcut, oracle, value, penalty, moment, clause,
    hpen, hmom, hcla, tolP, tolM, tolC⟩ := h n x bits hm
  have hfalse : (sources.hierarchy (fun n => n^(k+2)) clock).hierarchy.timedView.accepts n x = false :=
    Bool.eq_false_iff.mpr hno
  have hbelow := Soundness.below constants (outer sources k clock).result hcut x oracle hfalse
    value penalty moment clause hpen hmom tolP tolM tolC
  exact absurd hcla (not_le.mpr hbelow)

end
end NearCubicWires.RepairSource.CloseoutFinal
