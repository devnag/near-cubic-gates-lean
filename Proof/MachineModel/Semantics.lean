import Proof.MachineModel.Basic
import Proof.Circuits.DecompositionSourceEntry
import Proof.CaseAnalysis.RowsCircuitBottomMeaning
import Proof.CaseAnalysis.RawRowsChildren
import Proof.Supplier.RowCommonReusable

/-! P25: the frozen semantic input of the ordered decomposition-source batch.
Everything is stated with the existing definitions: the same selected
constructor `a.output`, the same bottom request `CloseoutRowsGateSource.request false`,
the checked `nativeWord`, and the two BottomMeaning output lists. No new
decomposition, no decoded output, no compression of arity to support. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open SupplierPipeline CompilerSemantics CanonicalWitnessCodec RadixSemantics
open RepairOrdinary.DecompositionSource RepairOrdinary.CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (a : DecompositionAlgorithm)

/-- The ordinary bottom request of one retained occurrence (arity `q`, weak-to-strict). -/
def request {q : ℕ} (g : SupportedNormalizedGate q) : ExactDecompositionRequest :=
  CloseoutRowsGateSource.request false g
/-- The exact ordered children the selected constructor returns for that request. -/
def children {q : ℕ} (g : SupportedNormalizedGate q) : List (ExactThresholdGate q) :=
  (a.output (request g)).children
/-- The concatenated native child cache in occurrence order. -/
def GS {q : ℕ} (occ : List (SupportedNormalizedGate q)) : List (ExactThresholdGate q) :=
  occ.flatMap (children a)
/-- The per-occurrence child counts in the same order (zeros keep their position). -/
def counts {q : ℕ} (occ : List (SupportedNormalizedGate q)) : List ℕ :=
  occ.map (fun g => (children a g).length)
/-- The total child count. -/
def B {q : ℕ} (occ : List (SupportedNormalizedGate q)) : ℕ := (GS a occ).length
/-- Children of occurrences before `i`. -/
def offset {q : ℕ} (occ : List (SupportedNormalizedGate q)) (i : ℕ) : ℕ :=
  ((occ.take i).map (fun g => (children a g).length)).sum
/-- The validated circuit's native bottom stream: count header, framed opaque top
payload, then one framed native word per retained occurrence in order. -/
def segment {q : ℕ} (occ : List (SupportedNormalizedGate q)) (top : List Bool) : List Bool :=
  natWord occ.length ++ frame top ++ occ.flatMap (fun g => frame (nativeWord g))

/-! ## Request identity and the strict convention -/

theorem request_arity {q : ℕ} (g : SupportedNormalizedGate q) : (request g).arity = q := rfl
theorem request_gate {q : ℕ} (g : SupportedNormalizedGate q) :
    (request g).gate = nonStrictAsStrict g.gate := rfl
theorem request_weight {q : ℕ} (g : SupportedNormalizedGate q) (i : Fin q) :
    (request g).gate.weight i = g.gate.weight i := rfl
theorem request_threshold {q : ℕ} (g : SupportedNormalizedGate q) :
    (request g).gate.threshold = g.gate.threshold - 1 := rfl
theorem nativeWord_eq {q : ℕ} (g : SupportedNormalizedGate q) :
    nativeWord g = thresholdWord (request g).gate := rfl
/-- The framed native word is exactly the constructor's framed input word. -/
theorem nativeWord_input {q : ℕ} (g : SupportedNormalizedGate q) :
    nativeWord g = natWord (request g).arity ++ DecompositionSource.Call.tail (request g) := by
  simp only [nativeWord_eq, thresholdWord, DecompositionSource.Call.tail, request_arity, List.append_assoc]

/-! ## Counts, totals, offsets -/

theorem counts_length {q : ℕ} (occ : List (SupportedNormalizedGate q)) : (counts a occ).length = occ.length := by
  simp [counts]
theorem B_eq_sum {q : ℕ} (occ : List (SupportedNormalizedGate q)) : B a occ = (counts a occ).sum := by
  simp [B, GS, counts, List.length_flatMap]
theorem GS_nil {q : ℕ} : GS a ([] : List (SupportedNormalizedGate q)) = [] := rfl
theorem GS_cons {q : ℕ} (g : SupportedNormalizedGate q) (occ : List (SupportedNormalizedGate q)) :
    GS a (g :: occ) = children a g ++ GS a occ := by simp [GS]
theorem counts_cons {q : ℕ} (g : SupportedNormalizedGate q) (occ : List (SupportedNormalizedGate q)) :
    counts a (g :: occ) = (children a g).length :: counts a occ := by simp [counts]
theorem offset_zero {q : ℕ} (occ : List (SupportedNormalizedGate q)) : offset a occ 0 = 0 := by simp [offset]
theorem offset_succ_cons {q : ℕ} (g : SupportedNormalizedGate q) (occ : List (SupportedNormalizedGate q)) (i : ℕ) :
    offset a (g :: occ) (i+1) = (children a g).length + offset a occ i := by simp [offset]
theorem offset_le {q : ℕ} (occ : List (SupportedNormalizedGate q)) (i : ℕ) : offset a occ i ≤ B a occ := by
  induction occ generalizing i with
  | nil => simp [offset, B, GS]
  | cons g occ ih =>
    cases i with
    | zero => simp [offset_zero]
    | succ i =>
      rw [offset_succ_cons, B, GS_cons, List.length_append]
      have := ih i
      unfold B at this
      omega

/-- Absolute child indices: `offset_i + j` names child `j` of occurrence `i`, in range. -/
theorem GS_index {q : ℕ} (occ : List (SupportedNormalizedGate q)) (i j : ℕ) (hi : i < occ.length)
    (hj : j < (children a occ[i]).length) :
    offset a occ i + j < (GS a occ).length ∧ (GS a occ)[offset a occ i + j]? = (children a occ[i])[j]? := by
  induction occ generalizing i with
  | nil => simp at hi
  | cons g occ ih =>
    cases i with
    | zero =>
      simp only [offset_zero, Nat.zero_add, List.getElem_cons_zero] at hj ⊢
      rw [GS_cons, List.length_append, List.getElem?_append_left hj]
      exact ⟨by omega, rfl⟩
    | succ i =>
      simp only [List.getElem_cons_succ] at hj
      have hi' : i < occ.length := by simpa using hi
      obtain ⟨hlt, heq⟩ := ih i hi' hj
      rw [offset_succ_cons, GS_cons, List.length_append, Nat.add_assoc,
        List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      exact ⟨by omega, heq⟩

theorem GS_index_lt {q : ℕ} (occ : List (SupportedNormalizedGate q)) (i j : ℕ) (hi : i < occ.length)
    (hj : j < (children a occ[i]).length) : offset a occ i + j < B a occ :=
  (GS_index a occ i j hi hj).1

theorem GS_getElem {q : ℕ} (occ : List (SupportedNormalizedGate q)) (i j : ℕ) (hi : i < occ.length)
    (hj : j < (children a occ[i]).length) :
    (GS a occ)[offset a occ i + j]'((GS_index a occ i j hi hj).1) = (children a occ[i])[j] := by
  obtain ⟨hlt, h⟩ := GS_index a occ i j hi hj
  rw [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

/-! ## The existing raw-rows child identity and pair-coded assignment -/

theorem occurrenceExactChildren_eq {q : ℕ} (occ : List (SupportedNormalizedGate q)) (index : Fin occ.length) :
    RepairSource.CloseoutRawRows.occurrenceExactChildren a occ index = children a (occ.get index) := rfl

theorem pair_assignment {q : ℕ} (occ : List (SupportedNormalizedGate q)) (input : BitInput q)
    (i j : ℕ) (hi : i < occ.length) (hj : j < (children a occ[i]).length) :
    RepairSource.CloseoutRawRows.occurrenceExactChildAssignment a occ input (Nat.pair i j) =
      ((GS a occ)[offset a occ i + j]'((GS_index a occ i j hi hj).1)).eval input := by
  have h := RepairSource.CloseoutRawRows.occurrenceExactChildAssignment_pair a occ input ⟨i, hi⟩ ⟨j, hj⟩
  rw [h, GS_getElem]
  rfl

/-! ## Cache word and the direct-bank native port -/

theorem exactListWord_GS {q : ℕ} (occ : List (SupportedNormalizedGate q)) :
    exactListWord (GS a occ) = natWord (B a occ) ++ (GS a occ).flatMap exactWord := rfl

theorem port_zero {n : ℕ} (gs : List (ExactThresholdGate n)) (j p F : ℕ) (tail out : List Bool)
    (indices : List (Fin gs.length)) :
    RowCommonReusable.data gs j p F tail out indices 0 = exactListWord gs := rfl

/-! ## The two actual modes: exactly the checked BottomMeaning lists -/

def symOcc {core : ℕ} (c : NormalizedSymmetricThresholdCircuit core) : List (SupportedNormalizedGate core) :=
  List.ofFn c.bottom
def thrOcc {core : ℕ} (c : NormalizedThresholdThresholdCircuit core) : List (SupportedNormalizedGate core) :=
  List.ofFn (fun i => c.bottom (retainedTopIndex c i))

theorem symmetric_segment {core : ℕ} (c : NormalizedSymmetricThresholdCircuit core)
    (words : List (List Bool)) (membership : List Bool) (memberPos : ℕ) (top : List Bool)
    (hd : ∀ i, decodeSupportedNormalizedGate core (value (words.getD i.val [])) = some (c.bottom i)) :
    natWord c.bottomCount ++ frame top ++
      (List.range c.bottomCount).flatMap (CloseoutRowsCircuitBottomLoop.outputs false core memberPos membership words) =
      segment (symOcc c) top := by
  rw [CloseoutRowsCircuitBottomLoop.symmetric_output c words membership memberPos hd]
  simp [segment, symOcc]

theorem threshold_segment {core : ℕ} (c : NormalizedThresholdThresholdCircuit core)
    (words : List (List Bool)) (top : List Bool)
    (hd : ∀ i, decodeSupportedNormalizedGate core (value (words.getD i.val [])) = some (c.bottom i)) :
    natWord c.bottomCount ++ frame top ++
      (List.range c.bottomCount).flatMap
        (CloseoutRowsCircuitBottomLoop.outputs true core 1 (frame (CloseoutRowsGateSupport.gateMembers c.top.support)) words) =
      natWord c.bottomCount ++ frame top ++ (thrOcc c).flatMap (fun g => frame (nativeWord g)) := by
  rw [CloseoutRowsCircuitBottomLoop.threshold_output c words hd]
  rfl

theorem symOcc_length {core : ℕ} (c : NormalizedSymmetricThresholdCircuit core) : (symOcc c).length = c.bottomCount := by
  simp [symOcc]
theorem thrOcc_length {core : ℕ} (c : NormalizedThresholdThresholdCircuit core) :
    (thrOcc c).length = c.top.support.card := by simp [thrOcc]
theorem GS_symOcc {core : ℕ} (c : NormalizedSymmetricThresholdCircuit core) :
    GS a (symOcc c) = (List.ofFn c.bottom).flatMap (children a) := rfl
theorem GS_thrOcc {core : ℕ} (c : NormalizedThresholdThresholdCircuit core) :
    GS a (thrOcc c) = (List.ofFn (fun i => c.bottom (retainedTopIndex c i))).flatMap (children a) := rfl

/-! ## Source-fixed bounds from the actual request word -/

theorem parameter_le_word {q : ℕ} (g : SupportedNormalizedGate q) :
    (request g).arity + (request g).gate.encodingBits + 1 ≤ (nativeWord g).length := by
  change q + (nonStrictAsStrict g.gate).encodingBits + 1 ≤ (thresholdWord (nonStrictAsStrict g.gate)).length
  rw [thresholdWord_length]
  omega

theorem word_le_frame (w : List Bool) : w.length ≤ (frame w).length := by
  rw [frame_length']; omega

theorem sourceBudget_le_frame {q : ℕ} (g : SupportedNormalizedGate q) :
    sourceBudget a (request g) ≤ a.coefficient * (frame (nativeWord g)).length ^ a.degree := by
  unfold sourceBudget
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  exact (parameter_le_word g).trans (word_le_frame _)

theorem children_le_budget {q : ℕ} (g : SupportedNormalizedGate q) :
    (children a g).length ≤ sourceBudget a (request g) :=
  (children_le_output _).trans (output_length a (request g))

theorem body_le_budget {q : ℕ} (g : SupportedNormalizedGate q) :
    ((children a g).flatMap exactWord).length ≤ sourceBudget a (request g) := by
  have h := output_length a (request g)
  rw [exactListWord, List.length_append] at h
  exact le_trans (Nat.le_add_left _ _) h

theorem cache_le_budget {q : ℕ} (g : SupportedNormalizedGate q) :
    (exactListWord (children a g)).length ≤ sourceBudget a (request g) := output_length a (request g)

/-- Every framed gate word is a sub-block of the frame region of its segment. -/
theorem frame_le_region {q : ℕ} (occ : List (SupportedNormalizedGate q)) (g : SupportedNormalizedGate q)
    (hg : g ∈ occ) : (frame (nativeWord g)).length ≤ (occ.flatMap (fun g => frame (nativeWord g))).length := by
  induction occ with
  | nil => simp at hg
  | cons h occ ih =>
    rw [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp hg with rfl | hg
    · omega
    · have := ih hg; omega

theorem segment_length {q : ℕ} (occ : List (SupportedNormalizedGate q)) (top : List Bool) :
    (segment occ top).length =
      (natWord occ.length).length + (frame top).length + (occ.flatMap (fun g => frame (nativeWord g))).length := by
  simp only [segment, List.length_append]

theorem length_le_region {q : ℕ} (occ : List (SupportedNormalizedGate q)) :
    occ.length ≤ (occ.flatMap (fun g => frame (nativeWord g))).length := by
  induction occ with
  | nil => simp
  | cons g occ ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have := frame_pos (nativeWord g)
    omega

end NearCubicWires.ExtDecompositionBatch
