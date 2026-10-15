import Proof.Amplification.RecoveryCaseOnePaddedOrdinaryState

/-! The direct padded Case-1 ordinary word consumer.
The entire Case-1 computation runs from an ordinary single-word input:
original hierarchy request, original PCP and canonical search, actual
amplifier, and the requested canonical Boolean output. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOnePaddedOrdinary
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def word {k : Nat} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (r : InputRequest) (address : List Bool) :=
  RecoveryCaseOneEntry.word (List.ofFn r.2) (H.time r.1).bits address

def budget {c d k target : Nat} (amplifier : OrdinaryScheduleAmplifier c d)
    (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : Nat) (hpad : k+3≤Cpad) (r : InputRequest)
    (hn : (RecoveryCaseOnePaddedBit.generated source amplifier H Cpad hpad r).arity≤target) (address : BitInput target) :=
  RecoveryCaseOneEntry.budget (List.ofFn r.2) (H.time r.1).bits (List.ofFn address)+2+
    RecoveryCaseOnePaddedBit.budget source amplifier H Cpad hpad r hn address

theorem ordinary_ready {c d k target : Nat} (amplifier : OrdinaryScheduleAmplifier c d)
    (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : Nat) (hpad : k+3≤Cpad) (r : InputRequest)
    (hn : (RecoveryCaseOnePaddedBit.generated source amplifier H Cpad hpad r).arity≤target) (address : BitInput target) :
    ∃ cost,cost≤budget source amplifier H Cpad hpad r hn address ∧ ∃ out,
      Ready RecoveryOracle.correctedSat
        (program source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier)) cost
        (input source amplifier.constructor.program k (word H r (List.ofFn address))) out ∧
      out (ports source amplifier.constructor.program k).outputTape=
        frame (RecoveryPipeline.padCore (RecoveryCaseOnePaddedBit.generated source amplifier H Cpad hpad r).function hn address).toNat.bits := by
  obtain ⟨parsed,hparsed,parsedWord,parsedAddress⟩ :=
    RecoveryCaseOneEntry.ready (List.ofFn r.2) (H.time r.1).bits (List.ofFn address)
  let ambient:=input source amplifier.constructor.program k (word H r (List.ofFn address))
  let a:=install (entrySlots source amplifier.constructor.program k) ambient parsed
  have ha:=hparsed.focus (entrySlots source amplifier.constructor.program k)
    (entry_injective source amplifier.constructor.program k) ambient
    (entry_input source amplifier.constructor.program k _)
  obtain ⟨ca,hca,haOracle⟩ := RecoveryPrefixCold.ordinary_ready (o:=RecoveryOracle.correctedSat)
    (ports source amplifier.constructor.program k) (first source amplifier.constructor.program k) _ _ ha
  obtain ⟨cb,hcb,evaluated,hevaluated,evaluatedValue⟩ :=
    RecoveryCaseOnePaddedBit.bit_ready source amplifier H Cpad hpad r hn address
  have hb:=hevaluated.focus (ports source amplifier.constructor.program k)
    (bitSlots source amplifier.constructor.program k) (bit_injective source amplifier.constructor.program k)
    (by rfl) a (bit_tapes source amplifier.constructor.program k _ _ _ parsed parsedWord parsedAddress)
  have ta:=Ready.call (ports source amplifier.constructor.program k)
    (pieces source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier)) 0
    (next source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier)) 0 1 haOracle (by intro q; rfl)
  have tb:=Ready.stop (ports source amplifier.constructor.program k)
    (pieces source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier)) 0
    (next source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier)) 1 hb (by intro q; rfl)
  have trace:=trans ta tb
  have hstart : controlConfig
      (RecoveryCalls.code (fun j=>(pieces source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier) j).states) 0)
      (initialConfiguration (pieces source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier) 0).machine ambient)=
      initialConfiguration (program source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier)).base.machine ambient := rfl
  rw [hstart] at trace
  refine ⟨(ca+1)+(cb+1),?_,install (bitSlots source amplifier.constructor.program k) a evaluated,?_,?_⟩
  · calc
      _ = ca+2+cb := by omega
      _ ≤ _ := Nat.add_le_add (Nat.add_le_add_right hca 2) hcb
  · refine ⟨_,trace,?_,fun _=>rfl,rfl⟩
    simp [program,Ports.program,graph,RecoveryCalls.machine,RecoveryCalls.stopped]
  · exact (install_slot (bitSlots source amplifier.constructor.program k)
      (bit_injective source amplifier.constructor.program k) a evaluated
      (RecoveryCaseOnePaddedBit.ports source amplifier.constructor.program k).outputTape).trans evaluatedValue

theorem ordinary_runs {c d k target : Nat} (amplifier : OrdinaryScheduleAmplifier c d)
    (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : Nat) (hpad : k+3≤Cpad) (r : InputRequest)
    (hn : (RecoveryCaseOnePaddedBit.generated source amplifier H Cpad hpad r).arity≤target) (address : BitInput target) :
    OrdinaryOracleRuns RecoveryOracle.correctedSat
      (program source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (word H r (List.ofFn address))
      (RecoveryPipeline.padCore (RecoveryCaseOnePaddedBit.generated source amplifier H Cpad hpad r).function hn address).toNat.bits
      (budget source amplifier H Cpad hpad r hn address) := by
  obtain ⟨cost,hcost,out,⟨final,trace,halted,_heads,htapes⟩,hout⟩ :=
    ordinary_ready source amplifier H Cpad hpad r hn address
  rw [input_tapes] at trace
  exact ⟨cost,final,hcost,trace,halted,by rw [htapes]; exact hout⟩

/-- Target arity is read from the address word; the program is fixed before
this request and its padding proof are supplied. -/
def Request {c d k : Nat} (amplifier : OrdinaryScheduleAmplifier c d)
    (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : Nat) (hpad : k+3≤Cpad) :=
  Σ r : InputRequest, Σ target : Nat,
    { _address : BitInput target //
      (RecoveryCaseOnePaddedBit.generated source amplifier H Cpad hpad r).arity≤target }

def function {c d k : Nat} (amplifier : OrdinaryScheduleAmplifier c d)
    (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : Nat) (hpad : k+3≤Cpad) :
    OrdinaryOracleWordFunction RecoveryOracle.correctedSat
      (Request source amplifier H Cpad hpad)
      (fun r=>word H r.1 (List.ofFn r.2.2.val))
      (fun r=>(RecoveryPipeline.padCore
        (RecoveryCaseOnePaddedBit.generated source amplifier H Cpad hpad r.1).function
        r.2.2.property r.2.2.val).toNat.bits)
      (fun r=>budget source amplifier H Cpad hpad r.1 r.2.2.property r.2.2.val) where
  program := program source amplifier.constructor.program k H.coefficient Cpad (VerifierEncoding.code H.verifier)
  realizes r := ordinary_runs source amplifier H Cpad hpad r.1 r.2.2.property r.2.2.val

end
end NearCubicWires.RepairSource.RecoveryCaseOnePaddedOrdinary
