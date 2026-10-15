import Proof.CaseAnalysis.RowsGateNativeCount
import Proof.CaseAnalysis.RowsGateDecisionMeaning

/-! Each physical stage and its original run theorem share ONE projected
state count. The cold controller consumes that package without comparing
independently expanded copies of the decoder state expression. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateColdStages
open LocalBitMultitape RadixSemantics CloseoutWitness CloseoutRowsGateSupport
open CanonicalBinary RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def FieldMeaning (bits : List Bool) (output : Fin 998 → List Bool) : Prop :=
  (readTapeBit (output 147) 0=true ↔ CompetitorWitnessTriple.structural bits) ∧
  (readTapeBit (output 367) 0=true ↔ (decodeIntList (value (CloseoutRowsGateHeader.codeWord bits 0))).isSome) ∧
  (readTapeBit (output 819) 0=true ↔ (decodeInt (value (CloseoutRowsGateHeader.codeWord bits 1))).isSome) ∧
  (readTapeBit (output 996) 0=true ↔ (decodeBoolList (value (CloseoutRowsGateHeader.codeWord bits 2))).isSome) ∧
  output 625=frame (RecoveryFixedUnpair.leftWord (CloseoutRowsGateHeader.codeWord bits 1)) ∧
  output 802=frame (CloseoutRowsIntegerGuard.payload (CloseoutRowsGateHeader.codeWord bits 1)) ∧
  output 808=NativeWord.word (CloseoutRowsIntegerGuard.payload (CloseoutRowsGateHeader.codeWord bits 1)) ∧
  output 994=frame (BitFields.payload (CloseoutRowsGateHeader.codeWord bits 2)) ∧
  output 861=CompareMachine.word (BitFields.payload (CloseoutRowsGateHeader.codeWord bits 2)).length ∧
  (∀ values,decodeIntList (value (CloseoutRowsGateHeader.codeWord bits 0))=some values →
    output 361=values.flatMap RepairRepresentation.intWord ∧ output 368=CompareMachine.word values.length) ∧
  (∀ z,decodeInt (value (CloseoutRowsGateHeader.codeWord bits 1))=some z →
    output 808=RepairRepresentation.natWord z.natAbs) ∧
  (∀ values,decodeBoolList (value (CloseoutRowsGateHeader.codeWord bits 2))=some values → output 994=frame values)

def FieldReceipt {s : ℕ} (p : Machine 998 s) : Prop := ∀ bits,∃ out,
  ClockJoin.ReadyRun p (CloseoutRowsGateFields.budget bits) (CloseoutRowsGateFields.input bits) out ∧
    FieldMeaning bits out
noncomputable def fieldStage : Σ s,{p : Machine 998 s // FieldReceipt p} :=
  ⟨_,CloseoutRowsGateFields.machine,CloseoutRowsGateFields.fields_run⟩

def NativeReceipt {s : ℕ} (compressed : Bool) (p : Machine 42 s) : Prop :=
  ∀ (fields : List (Bool×List Bool)) (membership source : List Bool) (n w : ℕ),
    (∀ field∈fields,field.2.length ≤ w) → ∃ out,
      ClockJoin.ReadyRun p (CloseoutRowsGateNative.framedBudget compressed fields membership source n w)
        (CloseoutRowsGateNative.framedInput fields membership source n) out ∧
      out 40=frame (CloseoutRowsGateNative.word compressed fields membership source n) ∧
      out 25=[validity fields membership true fields.length] ∧ out 1=CompareMachine.word fields.length
noncomputable def nativeStage (compressed : Bool) : Σ s,{p : Machine 42 s // NativeReceipt compressed p} :=
  ⟨_,CloseoutRowsGateNative.framedMachine compressed,by
    intro fields membership source n w hw
    obtain ⟨out,ho,ht,hf⟩ := CloseoutRowsGateNative.framed_run compressed fields membership source n w hw
    exact ⟨out,ho,ht,hf,CloseoutRowsGateNativeCount.retained_count compressed _ fields membership source n out ho⟩⟩

theorem field_run (bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun fieldStage.2.val (CloseoutRowsGateFields.budget bits) (CloseoutRowsGateFields.input bits) out ∧
      FieldMeaning bits out := fieldStage.2.property bits

theorem native_run (compressed : Bool) (fields : List (Bool×List Bool)) (membership source : List Bool)
    (n w : ℕ) (hw : ∀ field∈fields,field.2.length ≤ w) : ∃ out,
    ClockJoin.ReadyRun (nativeStage compressed).2.val
      (CloseoutRowsGateNative.framedBudget compressed fields membership source n w)
      (CloseoutRowsGateNative.framedInput fields membership source n) out ∧
      out 40=frame (CloseoutRowsGateNative.word compressed fields membership source n) ∧
      out 25=[validity fields membership true fields.length] ∧ out 1=CompareMachine.word fields.length :=
  (nativeStage compressed).2.property fields membership source n w hw

end NearCubicWires.RepairOrdinary.CloseoutRowsGateColdStages
