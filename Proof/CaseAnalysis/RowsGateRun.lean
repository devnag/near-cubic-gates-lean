import Proof.CaseAnalysis.RowsGatePair
import Proof.CaseAnalysis.RowsGateTyped

/-! Original raw gate code to the complete framed native request. The
four canonical field verdicts guard the arithmetic call. On the same
decoded supported gate, its exact native request and support flag return
under one ordinary receipt. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateCold
open LocalBitMultitape RecoveryRootRound RecoveryExecution CloseoutRowsGateSupport
open SupplierPipeline CanonicalBinary CanonicalWitnessCodec RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def actualFirst : Machine 1035 CloseoutRowsGateColdStages.fieldStage.1 :=
  RecoveryFocus.machine oldSlots CloseoutRowsGateColdStages.fieldStage.2.val
noncomputable def actualLast (compressed : Bool) : Machine 1035 (CloseoutRowsGateColdStages.nativeStage compressed).1 :=
  RecoveryFocus.machine slots (CloseoutRowsGateColdStages.nativeStage compressed).2.val
noncomputable def actualMachine (compressed : Bool) :=
  CloseoutRowsGateColdPair.machine actualFirst (actualLast compressed) guard

theorem cold_run {n : ℕ} (compressed : Bool) (g : SupportedNormalizedGate n) (bits : List Bool)
    (h : decodeSupportedNormalizedGate n (value bits)=some g) : ∃ out,
    ClockJoin.ReadyRun (actualMachine compressed) (budget compressed g bits) (input bits) out ∧
      out 1033=frame (CloseoutRowsGateNative.word compressed (gateFields g.gate) (gateMembers g.support)
        (signSource bits) g.gate.threshold.natAbs) ∧ out 1018=[true] := by
  obtain ⟨fields,hfields,hmeaning⟩ := CloseoutRowsGateColdStages.field_run bits
  obtain ⟨f0,f1,f2,f3,hw,hcount,hsign,_hs,hmag,hmembers,_hmcount⟩ :=
    CloseoutRowsGateColdStages.typed g bits h fields hmeaning
  let bank := install oldSlots (input bits) fields
  have prefixReady := hfields.focus oldSlots old_injective (input bits)
    (by intro i;simp only [input,oldSlots,Fin.addCases_left])
  have old (i : Fin 998) : bank (oldSlots i)=fields i := install_slot _ old_injective _ _ _
  obtain ⟨native,hnative,htarget,hflag,_nativeCount⟩ := CloseoutRowsGateColdStages.native_run compressed (gateFields g.gate)
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
  have requestReady := hnative.focus slots slots_injective bank hi
  have hguard : guard (fun i => readTapeBit (bank i) 0)=true := by
    change (readTapeBit (bank (oldSlots 147)) 0 && readTapeBit (bank (oldSlots 367)) 0 &&
      readTapeBit (bank (oldSlots 819)) 0 && readTapeBit (bank (oldSlots 996)) 0)=true
    rw [old,old,old,old,f0,f1,f2,f3]
    rfl
  have complete := CloseoutRowsGateColdPair.joined actualFirst (actualLast compressed) guard
    _ _ (input bits) bank (install slots bank native) prefixReady requestReady hguard
  refine ⟨install slots bank native,complete,?_,?_⟩
  · change install slots bank native (slots 40)=_
    exact (install_slot _ slots_injective _ _ 40).trans htarget
  · change install slots bank native (slots 25)=[true]
    rw [install_slot _ slots_injective,hflag,
      show (gateFields g.gate).length=n by simp [gateFields],gate_validity]

end NearCubicWires.RepairOrdinary.CloseoutRowsGateCold
