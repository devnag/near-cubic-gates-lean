import Proof.Amplification.RecoveryCaseOneBitState
import Proof.Amplification.RecoveryCaseOneSourceMeaning

/-! The actual hierarchy source, original canonical recovery, selected
amplifier and complete-table evaluator compute one requested Case-1 bit.
The request is that of the same global normalized outer PCP. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneBit
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def pcp {k : Nat} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : Nat) (hpad : k+3≤Cpad) :=
  normalizedSourcePCP source H (HierarchyEncode.encode H Cpad)
    (HierarchyProjection.width source H Cpad) (HierarchyProjection.queries source H Cpad)
    (HierarchyProjection.width_fits source H Cpad hpad) (HierarchyProjection.queries_fit source H Cpad hpad)
def generated {c d k : Nat} (amplifier : OrdinaryScheduleAmplifier c d)
    (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : Nat) (hpad : k+3≤Cpad) (r : InputRequest) :=
  let request:=RecoveryCaseOneRequest.request (pcp source H Cpad hpad) r.2
  amplifier.output request.inputArity request.function
def budget {c d k : Nat} (amplifier : OrdinaryScheduleAmplifier c d)
    (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : Nat) (hpad : k+3≤Cpad) (r : InputRequest)
    (address : BitInput (generated source amplifier H Cpad hpad r).arity) :=
  RecoveryCaseOneHierarchy.budget source amplifier k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad+2+
    RecoveryCaseOneEvaluation.budget (generated source amplifier H Cpad hpad r).function address

theorem bit_ready {c d k : Nat} (amplifier : OrdinaryScheduleAmplifier c d)
    (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : Nat) (hpad : k+3≤Cpad) (r : InputRequest)
    (address : BitInput (generated source amplifier H Cpad hpad r).arity) :
    ∃ cost,cost≤budget source amplifier H Cpad hpad r address ∧ ∃ out,
      Ready RecoveryOracle.correctedSat
        (program source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier)) cost
        (input source amplifier.constructor.program k (HierarchySourceInput.hierarchyInput H r) (List.ofFn address)) out ∧
      out ((25 : Fin 27).natAdd (base source amplifier.constructor.program k))=
        frame ((generated source amplifier H Cpad hpad r).function address).toNat.bits := by
  obtain ⟨ca,hca,constructed,hconstructed,constructedValue⟩ :=
    RecoveryCaseOneHierarchy.hierarchy_ready source amplifier H Cpad hpad r
  have hrq : RecoveryCaseOneRequest.request (pcp source H Cpad hpad) r.2=
      RecoveryCaseOneRequest.request
        (compactProjectionPCP (RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad r)) r.2 :=
    RecoveryCaseOneRequest.source_request source H (HierarchyEncode.encode H Cpad)
      (HierarchyProjection.width source H Cpad) (HierarchyProjection.queries source H Cpad)
      (HierarchyProjection.width_fits source H Cpad hpad) (HierarchyProjection.queries_fit source H Cpad hpad) r
  rw [←hrq] at constructedValue
  let ambient:=input source amplifier.constructor.program k (HierarchySourceInput.hierarchyInput H r) (List.ofFn address)
  let a:=install (sourceSlots source amplifier.constructor.program k) ambient constructed
  have ha:=hconstructed.focus (ports source amplifier.constructor.program k)
    (sourceSlots source amplifier.constructor.program k) (source_injective source amplifier.constructor.program k)
    (by rfl) ambient (source_input source amplifier.constructor.program k _ _)
  let f:=(generated source amplifier H Cpad hpad r).function
  have hv : constructed (RecoveryCaseOneHierarchy.ports source amplifier.constructor.program k).outputTape=
      frame (RecoveryCaseOneEvaluation.schema f) := constructedValue
  obtain ⟨evaluated,hevaluated,evaluatedValue⟩ := RecoveryCaseOneEvaluation.ready f address
  have hb:=hevaluated.focus (evalSlots source amplifier.constructor.program k)
    (eval_injective source amplifier.constructor.program k) a
    (eval_tapes source amplifier.constructor.program k (HierarchySourceInput.hierarchyInput H r) (List.ofFn address) _ constructed hv)
  obtain ⟨cb,hcb,hbOracle⟩ := RecoveryPrefixCold.ordinary_ready (o:=RecoveryOracle.correctedSat)
    (ports source amplifier.constructor.program k) (last source amplifier.constructor.program k) _ _ hb
  have ta:=Ready.call (ports source amplifier.constructor.program k)
    (pieces source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier)) 0
    (next source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier)) 0 1 ha (by intro q; rfl)
  have tb:=Ready.stop (ports source amplifier.constructor.program k)
    (pieces source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier)) 0
    (next source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier)) 1 hbOracle (by intro q; rfl)
  have trace:=trans ta tb
  have hstart : controlConfig
      (RecoveryCalls.code (fun j=>(pieces source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier) j).states) 0)
      (initialConfiguration (pieces source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier) 0).machine ambient)=
      initialConfiguration (program source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier)).base.machine ambient := rfl
  rw [hstart] at trace
  refine ⟨(ca+1)+(cb+1),?_,install (evalSlots source amplifier.constructor.program k) a evaluated,?_,?_⟩
  · calc
      _ = ca+2+cb := by omega
      _ ≤ _ := Nat.add_le_add (Nat.add_le_add_right hca 2) hcb
  · refine ⟨_,trace,?_,fun _=>rfl,rfl⟩
    simp [program,Ports.program,graph,RecoveryCalls.machine,RecoveryCalls.stopped]
  · have ht:=install_slot (evalSlots source amplifier.constructor.program k)
      (eval_injective source amplifier.constructor.program k) a evaluated 26
    rw [eval_output] at ht
    exact ht.trans evaluatedValue

end
end NearCubicWires.RepairSource.RecoveryCaseOneBit
