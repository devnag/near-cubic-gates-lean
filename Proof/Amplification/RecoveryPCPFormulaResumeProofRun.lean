import Proof.Amplification.RecoveryPCPFormulaResumeProofLayout

/-! Physical request production is consumed by the already accepted ordinary
canonical search on the same formula and proof count. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeProof
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem search_ready (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) : ∃ cost,
    cost≤budget R Q (Codec.clauses p).length
      (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x)
      (balancedCNFPayload (outerProofRecoveryFormula (compactProjectionPCP (p.normalized R Q hr hq)) x)) ∧
    ∃ out,Ready RecoveryOracle.correctedSat program cost (input p R Q) out ∧
      out (1181 : Fin 1184)=frame (RecoveryPrefixBody.search true
        (balancedCNFPayload (outerProofRecoveryFormula (compactProjectionPCP (p.normalized R Q hr hq)) x)) (2^R) []) := by
  let payload:=balancedCNFPayload (outerProofRecoveryFormula (compactProjectionPCP (p.normalized R Q hr hq)) x)
  obtain ⟨request,hrequest,r794⟩ := RecoveryPCPFormulaResumeSearchRequest.request_ready p R Q hr hq x
  let a:=install requestSlots (input p R Q) request
  have ha:=hrequest.focus requestSlots request_injective (input p R Q) (by
    intro i; simp only [requestSlots,input,Fin.addCases_left])
  obtain ⟨ca,hca,haOracle⟩ := RecoveryPrefixCold.ordinary_ready (o:=RecoveryOracle.correctedSat) ports requestMachine _ _ ha
  obtain ⟨cb,hcb,searched,hsearched,s386⟩ := RecoveryPrefixCold.whole_ready 1073741824 payload (2^R) true (Nat.le_refl _)
  have ht : ∀ i : Fin 389,a (prefixSlots i)=RecoveryPrefixCold.input payload (2^R) i := by
    intro i
    by_cases hi : i=0
    · subst i
      exact (install_slot requestSlots request_injective _ request 794).trans r794
    · have hiv : i.val≠0 := fun h=>hi (Fin.ext h)
      let j : Fin 388 := ⟨i.val-1,by have hib:=i.isLt; omega⟩
      have he : prefixSlots i=j.natAdd 796 := by
        apply Fin.ext
        simp only [prefixSlots,hi,ite_false,Fin.val_natAdd]
        dsimp [j]
        omega
      dsimp only [a]
      rw [he,install_other _ _ _ _ (by
        intro k hk
        have hv:=congrArg (fun i : Fin 1184=>i.val) hk
        have hkb:=k.isLt
        change k.val=796+j.val at hv
        omega)]
      simp only [input,Fin.addCases_right,RecoveryPrefixCold.input,hiv,ite_false]
  have hbOracle:=hsearched.focus ports prefixSlots prefix_injective (by rfl) a ht
  have trA:=Ready.call ports pieces 0 next 0 1 haOracle (by intro q; rfl)
  have trB:=Ready.stop ports pieces 0 next 1 hbOracle (by intro q; rfl)
  have trace:=trans trA trB
  have hstart : controlConfig (RecoveryCalls.code (fun j=>(pieces j).states) 0)
      (initialConfiguration (pieces 0).machine (input p R Q))=
      initialConfiguration program.base.machine (input p R Q) := rfl
  rw [hstart] at trace
  refine ⟨(ca+1)+(cb+1),?_,install prefixSlots a searched,?_,?_⟩
  · unfold budget
    dsimp only [payload] at hcb
    omega
  · refine ⟨_,trace,?_,fun _=>rfl,rfl⟩
    simp [program,Ports.program,graph,RecoveryCalls.machine,RecoveryCalls.stopped]
  · exact (install_slot prefixSlots prefix_injective a searched 386).trans s386

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeProof
