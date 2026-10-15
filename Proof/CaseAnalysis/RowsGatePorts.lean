import Proof.CaseAnalysis.RowsGateNativeRetained

/-! Project the same original weights, support bitmap and unsigned threshold
word through the accepted cold trace. No decoder or physical instruction
is rerun; the existing controller receipt is only strengthened. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateCold
open LocalBitMultitape RecoveryRootRound RecoveryExecution CloseoutRowsGateSupport
open SupplierPipeline CanonicalBinary CanonicalWitnessCodec RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cold_ports {n : ℕ} (compressed : Bool) (g : SupportedNormalizedGate n) (bits : List Bool)
    (h : decodeSupportedNormalizedGate n (value bits)=some g) : ∃ out,
    ClockJoin.ReadyRun (actualMachine compressed) (budget compressed g bits) (input bits) out ∧
      out 1033=frame (CloseoutRowsGateNative.word compressed (gateFields g.gate) (gateMembers g.support)
        (signSource bits) g.gate.threshold.natAbs) ∧ out 1018=[true] ∧
      out 361=(List.ofFn g.gate.weight).flatMap RepairRepresentation.intWord ∧
      out 994=frame (gateMembers g.support) ∧ out 808=RepairRepresentation.natWord g.gate.threshold.natAbs ∧
      out 368=RepairSource.VerifierDecoding.CompareMachine.word n ∧
      out 861=RepairSource.VerifierDecoding.CompareMachine.word n := by
  obtain ⟨fields,hfields,hmeaning⟩ := CloseoutRowsGateColdStages.field_run bits
  obtain ⟨f0,f1,f2,f3,hw,hcount,hsign,_hs,hmag,hmembers,hmcount⟩ :=
    CloseoutRowsGateColdStages.typed g bits h fields hmeaning
  let bank := install oldSlots (input bits) fields
  have prefixReady := hfields.focus oldSlots old_injective (input bits)
    (by intro i;simp only [input,oldSlots,Fin.addCases_left])
  have old (i : Fin 998) : bank (oldSlots i)=fields i := install_slot _ old_injective _ _ _
  obtain ⟨native,hnative,htarget,hflag,nativeCount⟩ := CloseoutRowsGateColdStages.native_run compressed (gateFields g.gate)
    (gateMembers g.support) (signSource bits) g.gate.threshold.natAbs g.gate.encodingBits
    (CloseoutRowsGateNative.field_bound g.gate)
  have hi : ∀ i,bank (slots i)=CloseoutRowsGateNative.framedInput (gateFields g.gate)
      (gateMembers g.support) (signSource bits) g.gate.threshold.natAbs i := by
    intro i
    rw [native_input]
    refine Fin.addCases (m := 5) (n := 37) (fun j => ?_) (fun j => ?_) i
    · simp only [slots,Fin.addCases_left,old]
      fin_cases j
      · exact hw.trans (gateFields_word g.gate).symm
      · change fields 368=RepairSource.VerifierDecoding.CompareMachine.word (gateFields g.gate).length
        simpa only [gateFields,List.length_ofFn] using hcount
      · exact hmembers
      · exact hsign
      · exact hmag
    · simp only [slots,Fin.addCases_right]
      exact fresh fields j
  have retained := CloseoutRowsGateNativeRetained.retained compressed _ (gateFields g.gate)
    (gateMembers g.support) (signSource bits) g.gate.threshold.natAbs native hnative
  obtain ⟨_,_,_,_,_,_,_,_,_,_,thresholdOriginal,_⟩ := hmeaning
  have requestReady := hnative.focus slots slots_injective bank hi
  have hguard : guard (fun i => readTapeBit (bank i) 0)=true := by
    change (readTapeBit (bank (oldSlots 147)) 0 && readTapeBit (bank (oldSlots 367)) 0 &&
      readTapeBit (bank (oldSlots 819)) 0 && readTapeBit (bank (oldSlots 996)) 0)=true
    rw [old,old,old,old,f0,f1,f2,f3]
    rfl
  have complete := CloseoutRowsGateColdPair.joined actualFirst (actualLast compressed) guard
    _ _ (input bits) bank (install slots bank native) prefixReady requestReady hguard
  refine ⟨install slots bank native,complete,?_,?_,?_,?_,?_,?_,?_⟩
  · change install slots bank native (slots 40)=_
    exact (install_slot _ slots_injective _ _ 40).trans htarget
  · change install slots bank native (slots 25)=[true]
    rw [install_slot _ slots_injective,hflag,
      show (gateFields g.gate).length=n by simp [gateFields],gate_validity]

  · exact (install_slot _ slots_injective _ _ 0).trans (retained.1.trans (gateFields_word g.gate))
  · exact (install_slot _ slots_injective _ _ 2).trans retained.2
  · rw [install_other _ _ _ _ (by decide)]
    change bank (oldSlots 808)=_
    rw [old]
    exact thresholdOriginal _ (CloseoutRowsGateGuard.typed_components g bits h).2.2.1
  · change install slots bank native (slots 1)=_
    rw [install_slot _ slots_injective,nativeCount]
    simp only [gateFields,List.length_ofFn]
  · rw [install_other _ _ _ _ (by decide)]
    exact (old 861).trans hmcount

end NearCubicWires.RepairOrdinary.CloseoutRowsGateCold
