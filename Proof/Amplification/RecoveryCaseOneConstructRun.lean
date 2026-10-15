import Proof.Amplification.RecoveryCaseOneConstructLayout

/-! Execute canonical recovery and the actual schedule amplifier in one
ordinary oracle graph, with an unconditional physical construction clock. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneConstruct
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def budget {c d : Nat} (amplifier : OrdinaryScheduleAmplifier c d)
    (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q) {n : Nat} (x : BitInput n) :=
  let pcp:=compactProjectionPCP (p.normalized R Q hr hq)
  RecoveryCaseOneInput.budget R Q (Codec.clauses p).length (RecoveryPCPFormulaResume.words pcp x)
    (balancedCNFPayload (outerProofRecoveryFormula pcp x)) (RecoveryCaseOneRequest.table pcp x)+2+
    RecoveryCaseOneAmplifier.budget amplifier (RecoveryCaseOneRequest.request pcp x)

theorem constructor_ready {c d : Nat} (amplifier : OrdinaryScheduleAmplifier c d)
    (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q) {n : Nat} (x : BitInput n) :
    ∃ cost,cost≤budget amplifier p R Q hr hq x ∧ ∃ out,
      Ready RecoveryOracle.correctedSat (program amplifier.constructor.program) cost
        (input amplifier.constructor.program p R Q) out ∧
      out ((RecoveryCaseOneAmplifier.output amplifier.constructor.program).natAdd 1193)=
        frame (amplifierOutput amplifier.toScheduleAmplifier
          (RecoveryCaseOneRequest.request (compactProjectionPCP (p.normalized R Q hr hq)) x)) := by
  obtain ⟨ca,hca,constructed,hconstructed,constructedValue⟩ := RecoveryCaseOneInput.input_ready p R Q hr hq x
  let ambient:=input amplifier.constructor.program p R Q
  let a:=install (inputSlots amplifier.constructor.program) ambient constructed
  have ha:=hconstructed.focus (ports amplifier.constructor.program) (inputSlots amplifier.constructor.program)
    (input_injective amplifier.constructor.program) (by rfl) ambient
    (input_tapes amplifier.constructor.program p R Q)
  let request:=RecoveryCaseOneRequest.request (compactProjectionPCP (p.normalized R Q hr hq)) x
  have ar : constructed (1191 : Fin 1193)=frame (amplifierInput request) := by
    rw [RecoveryCaseOneRequest.request_input]
    exact constructedValue
  obtain ⟨amplified,hamplified,amplifiedValue⟩ := RecoveryCaseOneAmplifier.constructor_ready amplifier request
  have hb:=hamplified.focus (amplifierSlots amplifier.constructor.program) (amplifier_injective amplifier.constructor.program)
    a (amplifier_input amplifier.constructor.program p R Q constructed _ ar)
  obtain ⟨cb,hcb,hbOracle⟩ := RecoveryPrefixCold.ordinary_ready (o:=RecoveryOracle.correctedSat)
    (ports amplifier.constructor.program) (last amplifier.constructor.program) _ _ hb
  have ta:=Ready.call (ports amplifier.constructor.program) (pieces amplifier.constructor.program) 0
    (next amplifier.constructor.program) 0 1 ha (by intro q; rfl)
  have tb:=Ready.stop (ports amplifier.constructor.program) (pieces amplifier.constructor.program) 0
    (next amplifier.constructor.program) 1 hbOracle (by intro q; rfl)
  have trace:=trans ta tb
  have hstart : controlConfig (RecoveryCalls.code (fun j=>(pieces amplifier.constructor.program j).states) 0)
      (initialConfiguration (pieces amplifier.constructor.program 0).machine ambient)=
      initialConfiguration (program amplifier.constructor.program).base.machine ambient := rfl
  rw [hstart] at trace
  refine ⟨(ca+1)+(cb+1),?_,install (amplifierSlots amplifier.constructor.program) a amplified,?_,?_⟩
  · calc
      _ = ca+2+cb := by omega
      _ ≤ _ := Nat.add_le_add (Nat.add_le_add_right hca 2) hcb
  · refine ⟨_,trace,?_,fun _=>rfl,rfl⟩
    simp [program,Ports.program,graph,RecoveryCalls.machine,RecoveryCalls.stopped]
  · have he : amplifierSlots amplifier.constructor.program (RecoveryCaseOneAmplifier.output amplifier.constructor.program)=
        (RecoveryCaseOneAmplifier.output amplifier.constructor.program).natAdd 1193 := by
      apply if_neg
      change amplifier.constructor.program.tapeCount+1+26≠0
      omega
    have ht:=install_slot (amplifierSlots amplifier.constructor.program) (amplifier_injective amplifier.constructor.program)
      a amplified (RecoveryCaseOneAmplifier.output amplifier.constructor.program)
    rw [he] at ht
    exact ht.trans amplifiedValue

end
end NearCubicWires.RepairSource.RecoveryCaseOneConstruct
