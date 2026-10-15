import Proof.Amplification.RecoveryCaseOneInputState

/-! One ordinary graph produces the actual selected-amplifier input.
Its execution and clock hold without an accepting-proof assumption. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneInput
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem input_ready (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) :
    let pcp:=compactProjectionPCP (p.normalized R Q hr hq)
    let payload:=balancedCNFPayload (outerProofRecoveryFormula pcp x)
    let table:=RecoveryPrefixBody.search true payload (2^R) []
    ∃ cost,cost≤budget R Q (Codec.clauses p).length
      (RecoveryPCPFormulaResume.words pcp x) payload table ∧ ∃ out,
      Ready RecoveryOracle.correctedSat program cost (input p R Q) out ∧
      out (1191 : Fin 1193)=frame (frame R.bits++table) := by
  intro pcp payload table
  obtain ⟨archive,harchive,arc0,arc1⟩ := RecoveryCaseOneArchive.archive_ready R.bits
  let a:=install archiveSlots (input p R Q) archive
  have ha:=harchive.focus archiveSlots archive_injective (input p R Q) (archive_input p R Q)
  obtain ⟨ca,hca,haOracle⟩ := RecoveryPrefixCold.ordinary_ready (o:=RecoveryOracle.correctedSat)
    ports archiveMachine _ _ ha
  obtain ⟨cb,hcb,proof,hproof,proofValue⟩ := RecoveryPCPFormulaResumeProof.search_ready p R Q hr hq x
  let b:=install proofSlots a proof
  have hbOracle:=hproof.focus ports proofSlots proof_injective (by rfl) a
    (archived_original p R Q archive arc0)
  obtain ⟨framed,hframed,framedValue⟩ := RecoveryCaseOnePayload.framed_ready R.bits table
  have hc:=hframed.focus payloadSlots payload_injective b (payload_input p R Q archive arc1 proof table proofValue)
  obtain ⟨cc,hcc,hcOracle⟩ := RecoveryPrefixCold.ordinary_ready (o:=RecoveryOracle.correctedSat)
    ports payloadMachine _ _ hc
  have ta:=Ready.call ports pieces 0 next 0 1 haOracle (by intro q; rfl)
  have tb:=Ready.call ports pieces 0 next 1 2 hbOracle (by intro q; rfl)
  have tc:=Ready.stop ports pieces 0 next 2 hcOracle (by intro q; rfl)
  have trace:=trans (trans ta tb) tc
  have hstart : controlConfig (RecoveryCalls.code (fun j=>(pieces j).states) 0)
      (initialConfiguration (pieces 0).machine (input p R Q))=
      initialConfiguration program.base.machine (input p R Q) := rfl
  rw [hstart] at trace
  refine ⟨((ca+1)+(cb+1))+(cc+1),?_,install payloadSlots b framed,?_,?_⟩
  · unfold budget
    dsimp only [pcp,payload]
    exact by omega
  · refine ⟨_,trace,?_,fun _=>rfl,rfl⟩
    simp [program,Ports.program,graph,RecoveryCalls.machine,RecoveryCalls.stopped]
  · exact (install_slot payloadSlots payload_injective b framed 6).trans framedValue

end
end NearCubicWires.RepairSource.RecoveryCaseOneInput
