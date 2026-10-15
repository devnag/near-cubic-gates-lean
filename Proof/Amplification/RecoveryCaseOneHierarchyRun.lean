import Proof.Amplification.RecoveryCaseOneHierarchyState

/-! The one selected hierarchy source is physically invoked before the
complete canonical recovery and the actual selected amplifier constructor. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneHierarchy
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def budget {c d : Nat} (amplifier : OrdinaryScheduleAmplifier c d)
    (k CH Cpad : Nat) (code : List Bool) {n : Nat} (x : BitInput n) (hpad : k+3≤Cpad) :=
  RecoveryPCPFormulaResumeProofSource.budget source k CH Cpad code (List.ofFn x)+2+
    RecoveryCaseOneConstruct.budget amplifier
      (source.output (HierarchyStreams.request k CH Cpad code (List.ofFn x)))
      (HierarchyStreams.R source k CH Cpad code (List.ofFn x))
      (HierarchyStreams.Q source k CH Cpad code (List.ofFn x))
      (Dimensions.width_fits source _ (RecoveryPCPFormulaResumeHierarchy.request_positive k CH Cpad code (List.ofFn x) hpad))
      (Dimensions.queries_fit source _ (RecoveryPCPFormulaResumeHierarchy.request_positive k CH Cpad code (List.ofFn x) hpad)) x

theorem output_slot (amp : OrdinaryProgram) (k : Nat) :
    constructSlots source amp k ((RecoveryCaseOneAmplifier.output amp).natAdd 1193)=
      ((RecoveryCaseOneAmplifier.output amp).natAdd 1193).natAdd (base source k) := by
  have hval : 1193≤((RecoveryCaseOneAmplifier.output amp).natAdd 1193).val := by simp
  unfold constructSlots
  split_ifs <;> first | rfl | omega

theorem constructor_ready {c d : Nat} (amplifier : OrdinaryScheduleAmplifier c d)
    (k CH Cpad : Nat) (code bound : List Bool) {n : Nat} (x : BitInput n) (hpad : k+3≤Cpad) :
    ∃ cost,cost≤budget source amplifier k CH Cpad code x hpad ∧ ∃ out,
      Ready RecoveryOracle.correctedSat (program source amplifier.constructor.program k CH Cpad code) cost
        (SourceHandoff.sourceTapes (frame (List.ofFn x)++frame bound)) out ∧
      out (((RecoveryCaseOneAmplifier.output amplifier.constructor.program).natAdd 1193).natAdd (base source k))=
        frame (amplifierOutput amplifier.toScheduleAmplifier (RecoveryCaseOneRequest.request
          (compactProjectionPCP (RecoveryPCPFormulaResumeHierarchy.normalized source k CH Cpad code (List.ofFn x) hpad)) x)) := by
  obtain ⟨src,hsrc,s0,s1,s2,s3,s4⟩ := RecoveryPCPFormulaResumeProofSource.source_ready source k CH Cpad code (List.ofFn x) bound hpad
  let ambient : Fin (tapes source amplifier.constructor.program k)→List Bool :=
    SourceHandoff.sourceTapes (frame (List.ofFn x)++frame bound)
  let a:=install (sourceSlots source amplifier.constructor.program k) ambient src
  have ha:=hsrc.focus (sourceSlots source amplifier.constructor.program k)
    (source_injective source amplifier.constructor.program k) ambient (by intro i; rfl)
  obtain ⟨ca,hca,haOracle⟩ := RecoveryPrefixCold.ordinary_ready (o:=RecoveryOracle.correctedSat)
    (ports source amplifier.constructor.program k) (sourceMachine source amplifier.constructor.program k CH Cpad code) _ _ ha
  obtain ⟨cb,hcb,constructed,hconstructed,constructedValue⟩ := RecoveryCaseOneConstruct.constructor_ready amplifier
    (source.output (HierarchyStreams.request k CH Cpad code (List.ofFn x)))
    (HierarchyStreams.R source k CH Cpad code (List.ofFn x))
    (HierarchyStreams.Q source k CH Cpad code (List.ofFn x))
    (Dimensions.width_fits source _ (RecoveryPCPFormulaResumeHierarchy.request_positive k CH Cpad code (List.ofFn x) hpad))
    (Dimensions.queries_fit source _ (RecoveryPCPFormulaResumeHierarchy.request_positive k CH Cpad code (List.ofFn x) hpad)) x
  have hbOracle:=hconstructed.focus (ports source amplifier.constructor.program k)
    (constructSlots source amplifier.constructor.program k) (construct_injective source amplifier.constructor.program k)
    (by rfl) a (construct_tapes source amplifier.constructor.program k (frame (List.ofFn x)++frame bound) _ _ _ src s0 s1 s2 s3 s4)
  have ta:=Ready.call (ports source amplifier.constructor.program k) (pieces source amplifier.constructor.program k CH Cpad code)
    0 (next source amplifier.constructor.program k CH Cpad code) 0 1 haOracle (by intro q; rfl)
  have tb:=Ready.stop (ports source amplifier.constructor.program k) (pieces source amplifier.constructor.program k CH Cpad code)
    0 (next source amplifier.constructor.program k CH Cpad code) 1 hbOracle (by intro q; rfl)
  have trace:=trans ta tb
  have hstart : controlConfig (RecoveryCalls.code (fun j=>(pieces source amplifier.constructor.program k CH Cpad code j).states) 0)
      (initialConfiguration (pieces source amplifier.constructor.program k CH Cpad code 0).machine ambient)=
      initialConfiguration (program source amplifier.constructor.program k CH Cpad code).base.machine ambient := rfl
  rw [hstart] at trace
  refine ⟨(ca+1)+(cb+1),?_,install (constructSlots source amplifier.constructor.program k) a constructed,?_,?_⟩
  · calc
      _ = ca+2+cb := by omega
      _ ≤ _ := Nat.add_le_add (Nat.add_le_add_right hca 2) hcb
  · refine ⟨_,trace,?_,fun _=>rfl,rfl⟩
    simp [program,Ports.program,graph,RecoveryCalls.machine,RecoveryCalls.stopped]
  · have ht:=install_slot (constructSlots source amplifier.constructor.program k)
      (construct_injective source amplifier.constructor.program k) a constructed
      ((RecoveryCaseOneAmplifier.output amplifier.constructor.program).natAdd 1193)
    rw [output_slot] at ht
    exact ht.trans constructedValue

end
end NearCubicWires.RepairSource.RecoveryCaseOneHierarchy
