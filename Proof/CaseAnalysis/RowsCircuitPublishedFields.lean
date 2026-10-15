import Proof.CaseAnalysis.RowsCircuitThresholdTopFields

/-! Exact projections from the original top publication into the common
body input. Retained count and original serialized count stay distinct. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitPublishedFields
open LocalBitMultitape RecoveryRootRound RepairRepresentation
open CanonicalWitnessCodec RadixSemantics CloseoutRowsCircuit CloseoutRowsGateSupport SupplierPipeline
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem pad_twice (C : ℕ) (bits : List Bool) : ZeroPadding.pad C (ZeroPadding.pad C bits)=ZeroPadding.pad C bits:=by
  have h:C ≤ (ZeroPadding.pad C bits).length:=by rw [ZeroPadding.pad_length];exact Nat.le_max_left _ _
  change ZeroPadding.pad C bits++List.replicate (C-(ZeroPadding.pad C bits).length) false=ZeroPadding.pad C bits
  rw [Nat.sub_eq_zero_of_le h]
  simp

theorem symmetric_other (C n : ℕ) (bits : List Bool) (A : Fin 1703 → List Bool) (bank : Fin 181 → List Bool)
    (i : Fin 1703) (hp : ∀ j,CloseoutRowsCircuitSymmetricTop.publishSlots j≠i)
    (hs : ∀ j,CloseoutRowsCircuitSymmetricTop.slots j≠i) :
    CloseoutRowsCircuitSymmetricTop.output C n bits A bank i=A i:=by
  rw [CloseoutRowsCircuitSymmetricTop.output,install_other _ _ _ _ hp,
    CloseoutRowsCircuitSymmetricTop.middle,install_other _ _ _ _ hs]

theorem threshold_other {n : ℕ} (C : ℕ) (A : Fin 1703 → List Bool) (bank : Fin 1049 → List Bool)
    (g : SupportedNormalizedGate n) (i : Fin 1703) (hp : ∀ j,topPublishSlots j≠i)
    (hs : ∀ j,gateSlots j≠i) : CloseoutRowsCircuitThresholdTop.output C A bank g i=A i:=by
  rw [CloseoutRowsCircuitThresholdTop.output,install_other _ _ _ _ hp,
    CloseoutRowsCircuitThresholdTop.middle,install_other _ _ _ _ hs]

theorem symmetric_publication (C n : ℕ) (bits : List Bool) (A : Fin 1703 → List Bool) (bank : Fin 181 → List Bool) :
    ∀ i : Fin 8,CloseoutRowsCircuitSymmetricTop.output C n bits A bank
      (![1701,1692,1702,1689,1694,1695,1696,622] i)=
      (![ZeroPadding.pad C (frame (CloseoutWitness.BitFields.payload bits)),List.replicate C false,
        ZeroPadding.pad C (List.replicate n true),[],List.replicate C true,List.replicate (C+1) false,
        List.replicate C false,List.replicate n true] : Fin 8 → List Bool) i:=by
  have port (j : Fin 12):CloseoutRowsCircuitSymmetricTop.output C n bits A bank
      (CloseoutRowsCircuitSymmetricTop.publishSlots j)=
      CloseoutRowsCircuitTopPublish.output C 0 0 (CloseoutRowsCircuitSymmetricTop.sources C n bits) j:=
    install_slot _ CloseoutRowsCircuitSymmetricTop.publish_injective _ _ j
  intro i;fin_cases i
  · change CloseoutRowsCircuitSymmetricTop.output C n bits A bank (CloseoutRowsCircuitSymmetricTop.publishSlots 7)=_
    rw [port];change ZeroPadding.pad C (ZeroPadding.pad C (frame (CloseoutWitness.BitFields.payload bits)))=_
    exact pad_twice C _
  · change CloseoutRowsCircuitSymmetricTop.output C n bits A bank (CloseoutRowsCircuitSymmetricTop.publishSlots 8)=_
    rw [port];change ZeroPadding.pad C (List.replicate C false)=_
    simp [ZeroPadding.pad]
  · exact port 9
  · exact port 10
  · exact port 5
  · exact port 6
  · exact port 11
  · exact port 4

theorem threshold_publication {n : ℕ} (C : ℕ) (bits : List Bool) (A : Fin 1703 → List Bool)
    (bank : Fin 1049 → List Bool) (g : SupportedNormalizedGate n)
    (hg : decodeSupportedNormalizedGate n (value bits)=some g)
    (meaning : CloseoutRowsGateMeasured.Output true n bits bank)
    (bitmap : CloseoutRowsGateBank.padded C bank 994=ZeroPadding.pad C (frame (gateMembers g.support))) :
    ∀ i : Fin 7,CloseoutRowsCircuitThresholdTop.output C A bank g
      (![1701,1692,1702,1689,1694,1695,1696] i)=
      (![ZeroPadding.pad C (frame (thresholdWord (CloseoutRowsGateSource.request true g).gate)),
        ZeroPadding.pad C (frame (gateMembers g.support)),ZeroPadding.pad C (List.replicate g.wireCount true),
        List.replicate (CloseoutRowsCircuitThresholdTop.weights g+CloseoutRowsCircuitThresholdTop.theta g) true,
        List.replicate C true,List.replicate (C+1) false,List.replicate C false] : Fin 7 → List Bool) i:=by
  obtain ⟨native,_weights,_theta,count⟩:=meaning.2.2 g hg
  have port (j : Fin 12):CloseoutRowsCircuitThresholdTop.output C A bank g (topPublishSlots j)=
      CloseoutRowsCircuitTopPublish.output C (CloseoutRowsCircuitThresholdTop.weights g)
        (CloseoutRowsCircuitThresholdTop.theta g) (CloseoutRowsCircuitThresholdTop.sources C bank) j:=
    install_slot _ topPublish_injective _ _ j
  intro i;fin_cases i
  · change CloseoutRowsCircuitThresholdTop.output C A bank g (topPublishSlots 7)=_
    rw [port]
    change ZeroPadding.pad C (ZeroPadding.pad C (bank 1033))=_
    change bank 1033=frame (thresholdWord (CloseoutRowsGateSource.request true g).gate) at native
    rw [native,pad_twice]
    rfl
  · change CloseoutRowsCircuitThresholdTop.output C A bank g (topPublishSlots 8)=_
    rw [port]
    change ZeroPadding.pad C (CloseoutRowsGateBank.padded C bank 994)=_
    rw [bitmap,pad_twice]
    rfl
  · change CloseoutRowsCircuitThresholdTop.output C A bank g (topPublishSlots 9)=_
    rw [port]
    change ZeroPadding.pad C (ZeroPadding.pad C (bank 1047))=_
    change bank 1047=List.replicate g.wireCount true at count
    rw [count,pad_twice]
    rfl
  · exact port 10
  · exact port 5
  · exact port 6
  · exact port 11

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitPublishedFields
