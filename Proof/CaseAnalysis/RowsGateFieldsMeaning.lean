import Proof.CaseAnalysis.RowsGateFieldsBudget
import Proof.CaseAnalysis.RowsGateSupportMeaning
import Proof.CaseAnalysis.RowsStrictNative

/-! The cold field stream is the same decoded supported gate. These exact
port identities feed the arity/support checks and strict native request,
without interpreting a second circuit or serializing a second field list. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateFieldsMeaning
open LocalBitMultitape RadixSemantics CanonicalBinary CanonicalWitnessCodec SupplierPipeline
open CloseoutWitness CloseoutRowsGateSupport RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def codes {n : ℕ} (g : SupportedNormalizedGate n) : Fin 3 → ℕ :=
  ![encodeIntList (List.ofFn g.gate.weight),encodeInt g.gate.threshold,encodeBoolList (gateMembers g.support)]

theorem field_codes {n : ℕ} (g : SupportedNormalizedGate n) (bits : List Bool)
    (h : value bits=encodeSupportedNormalizedGate g) :
    CompetitorWitnessTriple.structural bits ∧ ∀ i,value (CloseoutRowsGateHeader.codeWord bits i)=codes g i := by
  obtain ⟨hs,h0,h1,h2⟩ := CompetitorWitnessTriple.extracted_values bits (codes g 0) (codes g 1) (codes g 2) h
  refine ⟨hs,?_⟩
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem threshold_payload (bits : List Bool) (z : ℤ) (h : decodeInt (value bits)=some z) :
    CloseoutRowsIntegerGuard.payload bits=z.natAbs.bits := by
  have hc := encodeInt_of_decode h
  have hm : value (RecoveryFixedUnpair.rightWord bits)=encodeNat z.natAbs := by
    rw [(RecoveryFixedUnpair.word_values bits).2,←hc,encodeInt,Nat.unpair_pair]
  exact (BitFields.encoded_passes _ _ hm).2

theorem gate_run {n : ℕ} (g : SupportedNormalizedGate n) (bits : List Bool)
    (h : decodeSupportedNormalizedGate n (value bits)=some g) : ∃ out,
    ClockJoin.ReadyRun CloseoutRowsGateFields.machine (CloseoutRowsGateFields.budget bits)
      (CloseoutRowsGateFields.input bits) out ∧
      readTapeBit (out 147) 0=true ∧ readTapeBit (out 367) 0=true ∧
      readTapeBit (out 819) 0=true ∧ readTapeBit (out 996) 0=true ∧
      out 361=(List.ofFn g.gate.weight).flatMap RepairRepresentation.intWord ∧
      out 368=CompareMachine.word n ∧
      out 625=frame (RecoveryFixedUnpair.leftWord (CloseoutRowsGateHeader.codeWord bits 1)) ∧
      readTapeBit (out 625) 1=decide (g.gate.threshold<0) ∧
      out 802=frame g.gate.threshold.natAbs.bits ∧
      out 994=frame (gateMembers g.support) ∧ out 861=CompareMachine.word n := by
  have hcode := (encodeSupportedNormalizedGate_of_decode h).symm
  obtain ⟨hstruct,hcodes⟩ := field_codes g bits hcode
  have hw : decodeIntList (value (CloseoutRowsGateHeader.codeWord bits 0))=some (List.ofFn g.gate.weight) := by
    rw [hcodes 0]
    exact decodeIntList_encode _
  have ht : decodeInt (value (CloseoutRowsGateHeader.codeWord bits 1))=some g.gate.threshold := by
    rw [hcodes 1]
    exact decodeInt_encode _
  have hm : decodeBoolList (value (CloseoutRowsGateHeader.codeWord bits 2))=some (gateMembers g.support) := by
    rw [hcodes 2]
    exact decodeBoolList_encode _
  obtain ⟨out,hr,f0,f1,f2,f3,sign,payload,_,_,count,weights,_,support⟩ := CloseoutRowsGateFields.fields_run bits
  refine ⟨out,hr,f0.mpr hstruct,f1.mpr (by rw [hw];rfl),f2.mpr (by rw [ht];rfl),
    f3.mpr (by rw [hm];rfl),(weights _ hw).1,?_,sign,?_,?_,support _ hm,?_⟩
  · simpa only [List.length_ofFn] using (weights _ hw).2
  · rw [sign]
    exact CloseoutRowsSignedAppend.sign_of_decode _ _ ht
  · rw [payload,threshold_payload _ _ ht]
  · rw [count,(CloseoutRowsBooleanVector.checks_of_typed (gateMembers g.support)
      (CloseoutRowsGateHeader.codeWord bits 2) (hcodes 2)).2]
    simp only [gateMembers,List.length_ofFn]

end NearCubicWires.RepairOrdinary.CloseoutRowsGateFieldsMeaning
