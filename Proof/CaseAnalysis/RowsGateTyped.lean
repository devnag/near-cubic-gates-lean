import Proof.CaseAnalysis.RowsGateStages

/-! Exact typed projections of the opaque field-stage receipt. This uses
the same public decoder equality; it does not introduce another gate. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateColdStages
open LocalBitMultitape RadixSemantics CanonicalBinary CanonicalWitnessCodec SupplierPipeline
open CloseoutRowsGateSupport CloseoutWitness RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem typed {n : ℕ} (g : SupportedNormalizedGate n) (bits : List Bool)
    (h : decodeSupportedNormalizedGate n (value bits)=some g) (out : Fin 998 → List Bool)
    (hfields : FieldMeaning bits out) :
    readTapeBit (out 147) 0=true ∧ readTapeBit (out 367) 0=true ∧
    readTapeBit (out 819) 0=true ∧ readTapeBit (out 996) 0=true ∧
    out 361=(List.ofFn g.gate.weight).flatMap RepairRepresentation.intWord ∧
    out 368=CompareMachine.word n ∧
    out 625=frame (RecoveryFixedUnpair.leftWord (CloseoutRowsGateHeader.codeWord bits 1)) ∧
    readTapeBit (out 625) 1=decide (g.gate.threshold < 0) ∧
    out 802=frame g.gate.threshold.natAbs.bits ∧
    out 994=frame (gateMembers g.support) ∧ out 861=CompareMachine.word n := by
  have hcode := (encodeSupportedNormalizedGate_of_decode h).symm
  obtain ⟨hstruct,hcodes⟩ := CloseoutRowsGateFieldsMeaning.field_codes g bits hcode
  have hw : decodeIntList (value (CloseoutRowsGateHeader.codeWord bits 0))=some (List.ofFn g.gate.weight) := by
    rw [hcodes 0];exact decodeIntList_encode _
  have ht : decodeInt (value (CloseoutRowsGateHeader.codeWord bits 1))=some g.gate.threshold := by
    rw [hcodes 1];exact decodeInt_encode _
  have hm : decodeBoolList (value (CloseoutRowsGateHeader.codeWord bits 2))=some (gateMembers g.support) := by
    rw [hcodes 2];exact decodeBoolList_encode _
  obtain ⟨f0,f1,f2,f3,sign,payload,_,_,count,weights,_,support⟩ := hfields
  refine ⟨f0.mpr hstruct,f1.mpr (by rw [hw];rfl),f2.mpr (by rw [ht];rfl),
    f3.mpr (by rw [hm];rfl),(weights _ hw).1,?_,sign,?_,?_,support _ hm,?_⟩
  · simpa only [List.length_ofFn] using (weights _ hw).2
  · rw [sign]
    exact CloseoutRowsSignedAppend.sign_of_decode _ _ ht
  · rw [payload,CloseoutRowsGateFieldsMeaning.threshold_payload _ _ ht]
  · rw [count,(CloseoutRowsBooleanVector.checks_of_typed (gateMembers g.support)
      (CloseoutRowsGateHeader.codeWord bits 2) (hcodes 2)).2]
    simp only [gateMembers,List.length_ofFn]

end NearCubicWires.RepairOrdinary.CloseoutRowsGateColdStages
