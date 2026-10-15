import Proof.Wire_3_5.RecoveryCaseTwo
import Proof.CaseAnalysis.CaseOneHardness
import Proof.CaseAnalysis.CaseTwoDirect

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.OuterPCPRecovery (acceptsOracleCircuit projectedInput)
open NearCubicWires.RepairSource.RecoveryChoice (SmallOracle oracleSelector)
open NearCubicWires.RepairSource.CloseoutSampledWitness (massCap)
open NearCubicWires.ComponentwiseCircuitRestriction (restrictedSymmetricDescriptionCap
  restrictedThresholdDescriptionCap)
open NearCubicWires.RecoveryWitnessPolicy (symmetricDescriptionCap thresholdDescriptionCap)
open NearCubicWires.CircuitRestriction (symmetricWireFamily thresholdWireFamily)

section Slice
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}
variable (S : UnionSetup I) {N : ℕ} (z : BitInput N)

/-- **The selected oracle's substituted circuit is a tautology**: an oracle accepting every random string of a
decision-independent PCP makes the substituted request circuit accept every input. -/
theorem taut_of_accepts (hind : ∀ u v, S.pcp.decision z u = S.pcp.decision z v)
    (oracle : BooleanCircuit (S.pcp.nativeWidth N)) (hacc : ∀ r, acceptsOracleCircuit S.pcp z oracle r = true) :
    ∀ y, (S.request z oracle).circuit.eval y = true := by
  intro y
  show (PCPPRequestBoundary.request S.pcppAlg (PCPPSubstitution.compactSubstituted oracle (S.pcp.queryAddressBits z)
    (S.pcp.decision z fun _ => false))).circuit.eval y = true
  rw [PCPPRequestBoundary.request_eval, CompetitorSourceAverage.outer_eval S.pcp z oracle hind]
  have h := hacc (ProjectionPCPPadding.prefixBits (Nat.le_max_left _ _) y)
  unfold acceptsOracleCircuit at h
  unfold ProjectionPCP.accepts ProjectionPCP.queryAddress
  simp only [CompetitorSourceAverage.oracleProof_address]
  exact h

/-- **The core of one source length is hard in both classes** (Cases 1 and 2): at an input `z` the machine `M`
rejects although every accepting guess would make it accept, every circuit within the caps has agreement below
`1/2 + γ` with the core. -/
theorem core_bounds (P : FusedPrimitive I) (cparams : MaskedCompletenessParameters S.params) (M : OrdinaryWeakMachine)
    (hacc : ∀ g : UnionGuess S z, UnionAccepts S P z g → M.accepts N z) (hrej : ¬ M.accepts N z)
    (hind : ∀ u v, S.pcp.decision z u = S.pcp.decision z v)
    {c : ℕ} (amplifier : OrdinaryScheduleAmplifier c S.G) (copies clauseBits target symCap thrCap : ℕ) (gamma : ℝ)
    (normalization : ThresholdNormalizationContract) (spectrum : ExpanderSpectrumContract) (xs : XorSource)
    -- Case 1
    (hq : 1 ≤ S.pcp.nativeWidth N) (complete : ∃ proof, ∀ randomness, S.pcp.accepts z proof randomness)
    (hfit1 : (amplifier.output (RecoveryCaseOneRequest.request S.pcp z).inputArity
      (RecoveryCaseOneRequest.request S.pcp z).function).arity ≤ target)
    (hsym1 : 40 * (target + symCap + 2) ^ 4 ≤
      integerFloorRoot c (RecoveryScheduleEnvelope.oracleSizeBound S.G (S.pcp.nativeWidth N)))
    (hthr1 : 50 * (target + thrCap + 2) ^ 4 ≤
      integerFloorRoot c (RecoveryScheduleEnvelope.oracleSizeBound S.G (S.pcp.nativeWidth N)))
    (hadv1 : Real.rpow (RecoveryScheduleEnvelope.oracleSizeBound S.G (S.pcp.nativeWidth N) : ℝ) (-(1 : ℝ) / c) < gamma)
    -- Case 2
    (hcopies : 1 ≤ copies) (hζ0 : 0 < cparams.ζ) (hζ1 : cparams.ζ < 1 / 2)
    (heps : xorEpsilon (cparams.ζ : ℝ) copies < gamma)
    (hc2 : ∀ oracle : BooleanCircuit (S.pcp.nativeWidth N),
      oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound S.G (S.pcp.nativeWidth N) →
      (S.pcppOf z oracle).clauseBits ≤ clauseBits)
    (hfit2 : ∀ oracle : BooleanCircuit (S.pcp.nativeWidth N),
      oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound S.G (S.pcp.nativeWidth N) →
      copies * ((S.request z oracle).arity + clauseBits + 1) ≤ target)
    (ledS : ∀ oracle : BooleanCircuit (S.pcp.nativeWidth N),
      oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound S.G (S.pcp.nativeWidth N) →
      CaseTwoLedger S z oracle .sym P cparams (massCap cparams.ζ copies) symCap
        (restrictedSymmetricDescriptionCap (S.request z oracle).arity ((S.request z oracle).arity + clauseBits + 1)
          (2 ^ symmetricDescriptionCap ((S.request z oracle).arity + clauseBits + 1) symCap) symCap))
    (ledT : ∀ oracle : BooleanCircuit (S.pcp.nativeWidth N),
      oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound S.G (S.pcp.nativeWidth N) →
      CaseTwoLedger S z oracle .thr P cparams (massCap cparams.ζ copies) thrCap
        (restrictedThresholdDescriptionCap (S.request z oracle).arity ((S.request z oracle).arity + clauseBits + 1)
          (2 ^ thresholdDescriptionCap ((S.request z oracle).arity + clauseBits + 1) thrCap)
          (thresholdDescriptionCap ((S.request z oracle).arity + clauseBits + 1) thrCap))) :
    (∀ circuit : SymmetricThresholdCircuit target, circuit.wireCount ≤ symCap →
      agreement circuit.eval (CloseoutLanguage.core S.pcp S.pcppAlg amplifier z copies clauseBits target) <
        1 / 2 + gamma) ∧
    (∀ circuit : ThresholdThresholdCircuit target, circuit.wireCount ≤ thrCap →
      agreement circuit.eval (CloseoutLanguage.core S.pcp S.pcppAlg amplifier z copies clauseBits target) <
        1 / 2 + gamma) := by
  by_cases hsmall : SmallOracle S.pcp S.G z
  · set sel := oracleSelector S.pcp S.G z hsmall with hsel
    have hsize : sel.circuit.size ≤ RecoveryScheduleEnvelope.oracleSizeBound S.G (S.pcp.nativeWidth N) := sel.sizeBounded
    have htaut := taut_of_accepts S z hind sel.circuit (fun r => sel.accepts r)
    exact CloseoutLanguage.case_two_direct_hardness S.pcp S.pcppAlg amplifier z copies clauseBits target symCap thrCap
      hcopies xs cparams.ζ hζ0 hζ1 gamma heps hsmall (hc2 sel.circuit hsize) (hfit2 sel.circuit hsize)
      (no_sampled_sym S z sel.circuit normalization spectrum P cparams M hacc hrej hsize htaut clauseBits copies symCap
        (hc2 sel.circuit hsize) cparams.ζ hζ0 hζ1 le_rfl (ledS sel.circuit hsize))
      (no_sampled_thr S z sel.circuit normalization spectrum P cparams M hacc hrej hsize htaut clauseBits copies thrCap
        (hc2 sel.circuit hsize) cparams.ζ hζ0 hζ1 le_rfl (ledT sel.circuit hsize))
  · exact CloseoutCaseOne.core_hardness S.pcp S.pcppAlg amplifier z copies clauseBits target symCap thrCap normalization
      hq complete hsmall hfit1 hsym1 hthr1 gamma hadv1

end Slice

end NearCubicWires.WireExponent3_5.Transfer
