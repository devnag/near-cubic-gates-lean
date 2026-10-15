import Proof.CaseAnalysis.Xor
import Proof.CaseAnalysis.Language
import Proof.Amplification.XorResourcesProjection

/-! The exact canonical Case-2 core consumes the two local farness facts.
The unchanged XOR source uses the sharper checked coefficient policy and
the original constant mass cap; both physical classes keep the same table. -/
namespace NearCubicWires.RepairSource.CloseoutLanguage
open SourceInterfaces RepairRepresentation RepairOrdinary RepairXor CircuitRestriction
open RecoveryPipeline ComponentwiseTransfer
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem core_case_two {M : TimedDecisionMachine} {T : Nat→Nat} {c d n : Nat}
    (pcp : ProjectionPCP M T) (a : PointwisePCPPAlgorithm)
    (amplifier : OrdinaryScheduleAmplifier c d) (input : BitInput n)
    (copies clauseBits target : Nat) (hsmall : RecoveryChoice.SmallOracle pcp d input) :
    let oracle:=(RecoveryChoice.oracleSelector pcp d input hsmall).circuit
    let request:=PCPPSubstitution.sourceRequest a oracle (pcp.queryAddressBits input)
      (pcp.decision input (fun _=>false))
    let pcpp:=a.output request
    ∀ (hc : pcpp.clauseBits ≤ clauseBits) (hfit : copies*(request.arity+clauseBits+1) ≤ target),
      core pcp a amplifier input copies clauseBits target=
        padCore (xorPower (paddedUnsigned pcpp hc) copies) hfit := by
  intro oracle request pcpp hc hfit
  dsimp only [oracle,request,pcpp] at hc hfit
  simp only [core,dif_pos hsmall,dif_pos hc,dif_pos hfit]
  rfl

theorem case_two_core_hardness {M : TimedDecisionMachine} {T : Nat→Nat} {c d n : Nat}
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
      let q0:=request.arity+clauseBits+1
      FarFromCircuitSums symmetricWireFamily f symCap (xorTermBound delta q0 copies)
        (natBitLength (CloseoutXor.cap delta q0 copies)) (1/xorEpsilon (delta : ℝ) copies) (delta : ℝ) →
      FarFromCircuitSums thresholdWireFamily f thrCap (xorTermBound delta q0 copies)
        (natBitLength (CloseoutXor.cap delta q0 copies)) (1/xorEpsilon (delta : ℝ) copies) (delta : ℝ) →
      (∀ circuit : SymmetricThresholdCircuit target, circuit.wireCount ≤ symCap →
        agreement circuit.eval (core pcp a amplifier input copies clauseBits target) < 1/2+gamma) ∧
      (∀ circuit : ThresholdThresholdCircuit target, circuit.wireCount ≤ thrCap →
        agreement circuit.eval (core pcp a amplifier input copies clauseBits target) < 1/2+gamma) := by
  intro oracle request pcpp hc hfit f q0 hsym hthr
  have hs : AverageHardAt symmetricWireFamily (xorPower f copies) symCap (xorEpsilon (delta : ℝ) copies) :=
    CloseoutXor.xor_consumer_sharp source delta hd hh symmetricWireFamily
      symmetricWireFamily_literalProjectionClosed symmetricWireFamily_negationClosed f (by omega)
      copies symCap hcopies hsym
  have ht : AverageHardAt thresholdWireFamily (xorPower f copies) thrCap (xorEpsilon (delta : ℝ) copies) :=
    CloseoutXor.xor_consumer_sharp source delta hd hh thresholdWireFamily
      thresholdWireFamily_literalProjectionClosed thresholdWireFamily_negationClosed f (by omega)
      copies thrCap hcopies hthr
  have hsPad:=averageHard_padCore (family:=symmetricWireFamily) (size:=symCap)
    symmetricWireFamily_restrictionClosed hs hfit
  have htPad:=averageHard_padCore (family:=thresholdWireFamily) (size:=thrCap)
    thresholdWireFamily_restrictionClosed ht hfit
  have heq:=core_case_two pcp a amplifier input copies clauseBits target hsmall hc hfit
  rw [heq]
  have hstrict : 1/2+xorEpsilon (delta : ℝ) copies < 1/2+gamma := by linarith
  exact ⟨fun circuit hcap=>(hsPad circuit.eval ⟨circuit,hcap,rfl⟩).trans_lt hstrict,
    fun circuit hcap=>(htPad circuit.eval ⟨circuit,hcap,rfl⟩).trans_lt hstrict⟩

end
end NearCubicWires.RepairSource.CloseoutLanguage
