import Proof.Wire_3_5.PrimTCarrierFormat
import Proof.Wire_3_5.PrimTTabRef
import Proof.CaseAnalysis.RowsGateRawRun

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.CarGate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.CanonicalBinary NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairOrdinary.CloseoutRowsGateCold NearCubicWires.RepairOrdinary.CloseoutRowsGateSupport
open NearCubicWires.RepairSource.VerifierDecoding

/-- **The per-atom worker**: base's field decoder, then base's ordinary native writer, without the triple guard. -/
noncomputable def gateM := Composition.machine actualFirst (actualLast false)

/-- The ordinary native writer ignores the support word. -/
theorem word_members (fs : List (Bool × List Bool)) (m m' source : List Bool) (k : ℕ) :
    CloseoutRowsGateNative.word false fs m source k = CloseoutRowsGateNative.word false fs m' source k := rfl

/-- **The native word of an atom's decoded fields is its bottom-gate word.** -/
theorem word_eq {n : ℕ} (g : NormalizedThresholdGate n) (source : List Bool)
    (hs : readTapeBit source 1 = decide (g.threshold < 0)) :
    CloseoutRowsGateNative.word false (CloseoutRowsGateDecisionMeaning.fields (List.ofFn g.weight)) [] source
      g.threshold.natAbs = tabGW g := by
  have hf : CloseoutRowsGateDecisionMeaning.fields (List.ofFn g.weight) = gateFields g := by
    simp only [CloseoutRowsGateDecisionMeaning.fields, gateFields, List.map_ofFn, Function.comp_def]
  rw [hf, word_members (gateFields g) [] (gateMembers (Finset.univ : Finset (Fin n)))]
  exact CloseoutRowsGateNative.ordinary_word ⟨g, Finset.univ, fun i hi => absurd (Finset.mem_univ i) hi⟩ source hs

theorem encodeBoolList_nil : encodeBoolList [] = 0 := by
  simp [encodeBoolList, encodeBalancedList]

/-- **One atom's native word**: from an atom code's raw word, the worker writes `frame (tabGW g)` on tape `1033`. -/
theorem gate_run {n : ℕ} (g : NormalizedThresholdGate n) (bits : List Bool)
    (h : value bits = CarrierFormat.gateCode g) :
    ∃ out, ClockJoin.ReadyRun gateM (CloseoutRowsGateRawRun.budget bits) (CloseoutRowsGateCold.input bits) out ∧
      out 1033 = frame (tabGW g) := by
  obtain ⟨c0, c1, c2⟩ := CarrierFormat.gate_codeWords g bits h
  have hw : decodeIntList (value (CloseoutRowsGateHeader.codeWord bits 0)) = some (List.ofFn g.weight) := by
    rw [c0]; exact decodeIntList_encode _
  have ht : decodeInt (value (CloseoutRowsGateHeader.codeWord bits 1)) = some g.threshold := by
    rw [c1]; exact decodeInt_encode _
  have hm : decodeBoolList (value (CloseoutRowsGateHeader.codeWord bits 2)) = some [] := by
    rw [c2, ← encodeBoolList_nil]; exact decodeBoolList_encode _
  obtain ⟨fields, hf, meaning⟩ := CloseoutRowsGateColdStages.field_run bits
  obtain ⟨_, _, _, _, sign, payload, _, _, _, weightFields, _, supportFields⟩ := meaning
  set weights := List.ofFn g.weight with hws
  let fs := CloseoutRowsGateDecisionMeaning.fields weights
  have flen : fs.length = weights.length := List.length_map _
  have hwb : ∀ field ∈ fs, field.2.length ≤ bits.length + 2 := by
    simpa only [CloseoutRowsGateFields.field_length] using CloseoutRowsGateRawBounds.fields_bound _ weights hw
  have hwc : fs.length ≤ bits.length + 1 := by
    simpa only [fs, CloseoutRowsGateDecisionMeaning.fields, List.length_map, CloseoutRowsGateFields.field_length]
      using CloseoutRowsGateRawBounds.list_count _ weights hw
  have hmc : ([] : List Bool).length ≤ bits.length + 1 := Nat.zero_le _
  have htc : g.threshold.natAbs.bits.length ≤ bits.length + 1 := by
    simpa only [CloseoutRowsGateFields.field_length] using CloseoutRowsGateRawBounds.integer_bits _ g.threshold ht
  let bank := install oldSlots (input bits) fields
  have firstReady := hf.focus oldSlots old_injective (input bits)
    (by intro i; simp only [CloseoutRowsGateCold.input, oldSlots, Fin.addCases_left])
  have old (i : Fin 998) : bank (oldSlots i) = fields i := install_slot _ old_injective _ _ _
  obtain ⟨native, nr, nt, -, -⟩ := CloseoutRowsGateColdStages.native_run false fs []
    (signSource bits) g.threshold.natAbs (bits.length + 2) hwb
  have hi : ∀ i, bank (slots i) = CloseoutRowsGateNative.framedInput fs [] (signSource bits) g.threshold.natAbs i := by
    intro i
    rw [native_input]
    refine Fin.addCases (m := 5) (n := 37) (fun j => ?_) (fun j => ?_) i
    · simp only [slots, Fin.addCases_left, old]
      fin_cases j
      · exact (weightFields _ hw).1.trans (CloseoutRowsGateRawBounds.fields_word weights).symm
      · change fields 368 = CompareMachine.word fs.length
        rw [flen]; exact (weightFields _ hw).2
      · exact supportFields _ hm
      · exact sign
      · exact payload.trans (congrArg frame (CloseoutRowsGateFieldsMeaning.threshold_payload _ _ ht))
    · simp only [slots, Fin.addCases_right]
      exact fresh fields j
  have lastReady := nr.focus slots slots_injective bank hi
  have allReady := ClockJoin.join actualFirst (actualLast false) _ _ _ _ _ firstReady lastReady
  have htime := CloseoutRowsGateNativeBudget.framed_bound false fs [] (signSource bits)
    g.threshold.natAbs bits.length hwc hmc htc hwb
  refine ⟨install slots bank native, ClockJoin.enlarge _ _ (CloseoutRowsGateRawRun.budget bits) _ _ allReady
    (by unfold CloseoutRowsGateRawRun.budget; omega), ?_⟩
  rw [show (1033 : Fin 1035) = slots 40 from rfl, install_slot _ slots_injective _ _ 40, nt]
  exact congrArg frame (word_eq g _ (CloseoutRowsSignedAppend.sign_of_decode _ _ ht))

theorem budget_bound (bits : List Bool) :
    CloseoutRowsGateRawRun.budget bits ≤ 4000000000000000000001002 * (bits.length + 2) ^ 26 :=
  CloseoutRowsGateRawRun.budget_bound bits

end NearCubicWires.WireExponent3_5.PrimT.CarGate
