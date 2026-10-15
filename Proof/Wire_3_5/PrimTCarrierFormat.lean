import Proof.Wire_3_5.Shared.Carrier
import Proof.CaseAnalysis.CloseoutWitnessTraversal
import Proof.CaseAnalysis.RowsGateFieldsMeaning

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.CarrierFormat
open NearCubicWires NearCubicWires.CanonicalBinary NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.RepairOrdinary

/-! ## The code of a carrier -/

/-- **The code of one carrier atom**: its weight list and its threshold, as a tagged pair (the summand of
`Carrier.code`). -/
def gateCode {n : ℕ} (g : NormalizedThresholdGate n) : ℕ :=
  encodeTaggedList [encodeIntList (List.ofFn g.weight), encodeInt g.threshold]

/-- **A carrier's code is the balanced list of its atoms' codes.** -/
theorem code_eq {n : ℕ} (X : Carrier n) : X.code = encodeBalancedList (X.map gateCode) := rfl

/-- The pairing cells of an atom code: the tag `1`, the weight list, the tag `1`, the threshold, the empty tail. -/
theorem gateCode_pair {n : ℕ} (g : NormalizedThresholdGate n) :
    gateCode g = Nat.pair 1 (Nat.pair (encodeIntList (List.ofFn g.weight))
      (Nat.pair 1 (Nat.pair (encodeInt g.threshold) 0))) := rfl

/-- The weight list's code: the balanced list of the weights' signed codes. -/
theorem weights_list {n : ℕ} (g : NormalizedThresholdGate n) :
    encodeIntList (List.ofFn g.weight) = encodeBalancedList ((List.ofFn g.weight).map encodeInt) := rfl

/-- The threshold's code: its sign bit paired with its magnitude's code. -/
theorem threshold_pair {n : ℕ} (g : NormalizedThresholdGate n) :
    encodeInt g.threshold = Nat.pair (if g.threshold < 0 then 1 else 0) (encodeNat g.threshold.natAbs) := rfl

/-! ## The field boundaries -/

/-- **The field boundaries of an atom code** as base's triple extractor reads them: the tags at fields 0 and 2, the
weight list at field 1, the threshold at field 3, and the empty tail `0` at fields 4, 5 and node 6. -/
theorem gate_fields {n : ℕ} (g : NormalizedThresholdGate n) (bits : List Bool)
    (h : RadixSemantics.value bits = gateCode g) :
    CompetitorWitnessTriple.field bits 0 = 1 ∧
      CompetitorWitnessTriple.field bits 1 = encodeIntList (List.ofFn g.weight) ∧
      CompetitorWitnessTriple.field bits 2 = 1 ∧ CompetitorWitnessTriple.field bits 3 = encodeInt g.threshold ∧
      CompetitorWitnessTriple.field bits 4 = 0 ∧ CompetitorWitnessTriple.field bits 5 = 0 ∧
      CompetitorWitnessTriple.node bits 6 = 0 := by
  simp only [CompetitorWitnessTriple.field_eq, CompetitorWitnessTriple.node_eq, h, CompetitorWitnessTriple.nodeCode,
    gateCode_pair, Nat.unpair_pair, Nat.unpair_zero, Prod.fst_zero, Prod.snd_zero]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- **The gate header's three field words on an atom code**: the weight list, the threshold, and `0`. -/
theorem gate_codeWords {n : ℕ} (g : NormalizedThresholdGate n) (bits : List Bool)
    (h : RadixSemantics.value bits = gateCode g) :
    RadixSemantics.value (CloseoutRowsGateHeader.codeWord bits 0) = encodeIntList (List.ofFn g.weight) ∧
      RadixSemantics.value (CloseoutRowsGateHeader.codeWord bits 1) = encodeInt g.threshold ∧
      RadixSemantics.value (CloseoutRowsGateHeader.codeWord bits 2) = 0 := by
  obtain ⟨_, h1, _, h3, _, h5, _⟩ := gate_fields g bits h
  exact ⟨h1, h3, h5⟩

/-! ## The decoders' round trips -/

theorem decode_code {n : ℕ} (X : Carrier n) : decodeBalancedList X.code = some (X.map gateCode) :=
  decodeBalancedList_encode _

/-- The balanced traversal's atoms of a carrier code are its atoms' codes. -/
theorem tree_atoms_code {n : ℕ} (X : Carrier n) :
    (PCPPNativeCanonicalTree.tree X.code).atoms = X.map gateCode :=
  PCPPNativeCanonicalTree.tree_atoms _

/-- **The atom stream of a carrier code** (what base's traversal writes): the atoms' codes as `w`-bit framed words. -/
theorem atomStream_code {n : ℕ} (w : ℕ) (X : Carrier n) :
    PCPPNativeCanonicalWalk.atomStream w (PCPPNativeCanonicalTree.tree X.code).atoms =
      X.flatMap fun g => frame (SignedSortKey.binary w (gateCode g)) := by
  rw [tree_atoms_code, PCPPNativeCanonicalWalk.atomStream, List.flatMap_map]

theorem decodeTaggedList_gateCode {n : ℕ} (g : NormalizedThresholdGate n) :
    decodeTaggedList (gateCode g) = some [encodeIntList (List.ofFn g.weight), encodeInt g.threshold] :=
  decodeTaggedList_encode _

theorem decode_weights {n : ℕ} (g : NormalizedThresholdGate n) :
    decodeIntList (encodeIntList (List.ofFn g.weight)) = some (List.ofFn g.weight) :=
  decodeIntList_encode _

theorem decode_threshold {n : ℕ} (g : NormalizedThresholdGate n) :
    decodeInt (encodeInt g.threshold) = some g.threshold :=
  decodeInt_encode _

/-! ## The writer's sources -/

/-- **A supported gate's code carries the atom's two fields first**, then its support bitmap. -/
theorem supported_fields {n : ℕ} (sg : SupportedNormalizedGate n) :
    decodeTaggedList (encodeSupportedNormalizedGate sg) = some [encodeIntList (List.ofFn sg.gate.weight),
      encodeInt sg.gate.threshold, encodeBoolList (List.ofFn fun i => decide (i ∈ sg.support))] :=
  decodeTaggedList_encode _

/-- **An atom's code is the tagged pair of the first two fields of the bottom code it comes from.** -/
theorem gateCode_supported {n : ℕ} (sg : SupportedNormalizedGate n) :
    gateCode sg.gate = encodeTaggedList (((decodeTaggedList (encodeSupportedNormalizedGate sg)).getD []).take 2) := by
  rw [supported_fields]
  rfl

/-- The same on the gate header's field words of a bottom code (base `field_codes`). -/
theorem supported_codeWords {n : ℕ} (sg : SupportedNormalizedGate n) (bits : List Bool)
    (h : RadixSemantics.value bits = encodeSupportedNormalizedGate sg) :
    gateCode sg.gate = encodeTaggedList [RadixSemantics.value (CloseoutRowsGateHeader.codeWord bits 0),
      RadixSemantics.value (CloseoutRowsGateHeader.codeWord bits 1)] := by
  obtain ⟨_, hc⟩ := CloseoutRowsGateFieldsMeaning.field_codes sg bits h
  rw [hc 0, hc 1]
  rfl

/-- The fields of a `SYM∘THR` circuit code: the family tag, the bottom count, the bottoms' codes, the top table. -/
theorem sym_fields {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) :
    decodeTaggedList (encodeNormalizedSymmetricThresholdCircuit C) = some [encodeNat symmetricCircuitFamilyTag,
      encodeNat C.bottomCount, encodeBalancedList (List.ofFn fun i => encodeSupportedNormalizedGate (C.bottom i)),
      encodeBoolList (List.ofFn C.top)] :=
  decodeTaggedList_encode _

/-- The fields of a `THR∘THR` circuit code: the family tag, the bottom count, the bottoms' codes, the top's code. -/
theorem thr_fields {n : ℕ} (C : NormalizedThresholdThresholdCircuit n) :
    decodeTaggedList (encodeNormalizedThresholdThresholdCircuit C) = some [encodeNat thresholdCircuitFamilyTag,
      encodeNat C.bottomCount, encodeBalancedList (List.ofFn fun i => encodeSupportedNormalizedGate (C.bottom i)),
      encodeSupportedNormalizedGate C.top] :=
  decodeTaggedList_encode _

/-- The atoms' codes of a `SYM∘THR` circuit's charged gates: every bottom's, in order. -/
theorem symGates_codes {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) :
    (symGates C).map gateCode = List.ofFn fun i => gateCode (C.bottom i).gate := by
  simp only [symGates, List.map_map, List.ofFn_eq_map, Function.comp_def]

/-- The atoms' codes of a `THR∘THR` circuit's charged gates: the retained bottoms' (the top's support), in order. -/
theorem thrGates_codes {n : ℕ} (C : NormalizedThresholdThresholdCircuit n) :
    (thrGates C).map gateCode = ((List.finRange C.bottomCount).filter fun i => decide (i ∈ C.top.support)).map
      fun i => gateCode (C.bottom i).gate := by
  simp only [thrGates, List.map_map, Function.comp_def]

/-- **A carrier collected from several gate lists** is the balanced list of their atoms' codes, in order. -/
theorem code_flatten {n : ℕ} (Ys : List (Carrier n)) :
    Carrier.code Ys.flatten = encodeBalancedList (Ys.map fun Y => Y.map gateCode).flatten := by
  rw [code_eq, List.map_flatten]

end NearCubicWires.WireExponent3_5.PrimT.CarrierFormat
