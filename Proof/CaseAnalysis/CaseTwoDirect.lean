import Proof.CaseAnalysis.CaseTwoHardness

/-! The final consumer needs only the sampled sum returned by the actual
XOR source. Rejecting that sum avoids an unnecessary stronger farness claim
about every rational sum inside a rounded bit envelope. -/
namespace NearCubicWires.RepairSource.CloseoutLanguage
open SourceInterfaces RepairRepresentation RepairOrdinary RepairXor CircuitRestriction
open RecoveryPipeline ComponentwiseTransfer
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem xor_hardness_from_sampled (source : XorSource)
    (delta : ℚ) (hd : 0 < delta) (hh : delta < 1/2)
    (family : SizedFunctionFamily) (hprojection : LiteralProjectionClosed family)
    (hnegation : NegationClosedFamily family) {n : Nat} (f : BoolFunction n)
    (hn : 1 ≤ n) (copies size : Nat) (hc : 1 ≤ copies)
    (reject : SampledXorSum family delta n copies size f→False) :
    AverageHardAt family (xorPower f copies) size (xorEpsilon (delta : ℝ) copies) := by
  intro candidate hcandidate
  by_contra h
  obtain ⟨w⟩:=source delta hd hh family hprojection hnegation f hn copies size hc
    candidate hcandidate (lt_of_not_ge h)
  exact reject w

theorem case_two_direct_hardness {M : TimedDecisionMachine} {T : Nat→Nat} {c d n : Nat}
    (pcp : ProjectionPCP M T) (a : PointwisePCPPAlgorithm)
    (amplifier : OrdinaryScheduleAmplifier c d) (input : BitInput n)
    (copies clauseBits target symCap thrCap : Nat) (hcopies : 1 ≤ copies)
    (source : XorSource) (delta : ℚ) (hd : 0 < delta) (hh : delta < 1/2)
    (gamma : ℝ) (hepsilon : xorEpsilon (delta : ℝ) copies < gamma)
    (hsmall : RecoveryChoice.SmallOracle pcp d input) :
    let oracle:=(RecoveryChoice.oracleSelector pcp d input hsmall).circuit
    let request:=PCPPSubstitution.sourceRequest a oracle (pcp.queryAddressBits input)
      (pcp.decision input (fun _=>false))
    let pcpp:=a.output request
    ∀ (hc : pcpp.clauseBits ≤ clauseBits) (_hfit : copies*(request.arity+clauseBits+1) ≤ target),
      let f:=paddedUnsigned pcpp hc
      (SampledXorSum symmetricWireFamily delta (request.arity+clauseBits+1) copies symCap f→False) →
      (SampledXorSum thresholdWireFamily delta (request.arity+clauseBits+1) copies thrCap f→False) →
      (∀ circuit : SymmetricThresholdCircuit target, circuit.wireCount ≤ symCap →
        agreement circuit.eval (core pcp a amplifier input copies clauseBits target) < 1/2+gamma) ∧
      (∀ circuit : ThresholdThresholdCircuit target, circuit.wireCount ≤ thrCap →
        agreement circuit.eval (core pcp a amplifier input copies clauseBits target) < 1/2+gamma) := by
  intro oracle request pcpp hc hfit f hsym hthr
  have hs:=xor_hardness_from_sampled source delta hd hh symmetricWireFamily
    symmetricWireFamily_literalProjectionClosed symmetricWireFamily_negationClosed f (by omega)
    copies symCap hcopies hsym
  have ht:=xor_hardness_from_sampled source delta hd hh thresholdWireFamily
    thresholdWireFamily_literalProjectionClosed thresholdWireFamily_negationClosed f (by omega)
    copies thrCap hcopies hthr
  have hsPad:=averageHard_padCore (family:=symmetricWireFamily) (size:=symCap)
    symmetricWireFamily_restrictionClosed hs hfit
  have htPad:=averageHard_padCore (family:=thresholdWireFamily) (size:=thrCap)
    thresholdWireFamily_restrictionClosed ht hfit
  rw [core_case_two pcp a amplifier input copies clauseBits target hsmall hc hfit]
  have hstrict : 1/2+xorEpsilon (delta : ℝ) copies < 1/2+gamma := by linarith
  exact ⟨fun circuit hcap=>(hsPad circuit.eval ⟨circuit,hcap,rfl⟩).trans_lt hstrict,
    fun circuit hcap=>(htPad circuit.eval ⟨circuit,hcap,rfl⟩).trans_lt hstrict⟩

end
end NearCubicWires.RepairSource.CloseoutLanguage
