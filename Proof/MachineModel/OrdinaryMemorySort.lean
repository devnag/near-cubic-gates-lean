import Proof.MachineModel.OrdinaryMemoryLog
import Proof.MachineModel.OrdinaryCoordinateKey

/-! Apply the existing ordinary sorter to chronological memory events.
The two payload bits are read/after; the remaining key is timestamp/cell.
The timestamp is the event's actual position, not an unchecked witness field.
-/
namespace NearCubicWires.RepairOrdinary.MemorySort
open LocalBitMultitape StablePartition RadixSemantics SignedSortKey MemoryLog
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cellCode (W : ℕ) (cell : Cell) : ℕ := cell.1 * 2^W + cell.2

def encoded (I K W timestamp : ℕ) (e : Event) : Record :=
  (e.read, e.after :: (binary I timestamp ++ binary K (cellCode W e.cell)))

theorem encoded_key (I K W timestamp : ℕ) (e : Event) :
    encoded I K W timestamp e =
      CoordinateKey.key (I+1) K (2*timestamp+e.after.toNat) (cellCode W e.cell) e.read := by
  cases h : e.after <;>
    simp [encoded, CoordinateKey.key, binary, h, Nat.add_div]

@[simp] theorem encoded_width (I K W timestamp : ℕ) (e : Event) :
    (word (encoded I K W timestamp e)).length = I+K+2 := by
  simp [encoded, word]

def decodeIndex (N I : ℕ) (r : Record) : Option (Fin N) :=
  let timestamp := value (((word r).drop 2).take I)
  if h : timestamp < N then some ⟨timestamp, h⟩ else none

theorem decode_encoded {N : ℕ} (I K W : ℕ) (i : Fin N) (e : Event)
    (hN : N ≤ 2^I) : decodeIndex N I (encoded I K W i.val e) = some i := by
  have ht : value (((word (encoded I K W i.val e)).drop 2).take I) = i.val := by
    simp only [encoded, word, List.drop_succ_cons, List.drop_zero]
    rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
    exact binary_value I i.val (i.isLt.trans_le hN)
  simp only [decodeIndex, ht, i.isLt, ↓reduceDIte]

def request {N : ℕ} (I K W : ℕ) (events : Fin N → Event) : SortCarrier.Request :=
  DominanceSort.fixedRequest
    ((List.finRange N).map (fun i => encoded I K W i.val (events i))) (I+K+2) (by
      intro r hr
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
      exact encoded_width _ _ _ _ _)

noncomputable def sortedIndices {N : ℕ} (I K W : ℕ) (events : Fin N → Event) : List (Fin N) :=
  (SortCarrier.sorted (request I K W events)).filterMap (decodeIndex N I)

theorem sorted_output {N : ℕ} (I K W : ℕ) (events : Fin N → Event) (hN : N ≤ 2^I) :
    (sortedIndices I K W events).map (fun i => encoded I K W i.val (events i)) =
      SortCarrier.sorted (request I K W events) := by
  let req := request I K W events
  have hp := SortCarrier.sorted_perm req
  rw [sortedIndices, List.map_filterMap]
  calc
    _ = (SortCarrier.sorted req).filterMap some := by
      apply List.filterMap_congr
      intro r hr
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp (hp.mem_iff.mp hr)
      rw [decode_encoded I K W i (events i) hN]
      rfl
    _ = _ := List.filterMap_some

theorem sorted_perm {N : ℕ} (I K W : ℕ) (events : Fin N → Event) (hN : N ≤ 2^I) :
    (sortedIndices I K W events).Perm (List.finRange N) := by
  have hp := (SortCarrier.sorted_perm (request I K W events)).filterMap (decodeIndex N I)
  have hin : (request I K W events).records.filterMap (decodeIndex N I) = List.finRange N := by
    change ((List.finRange N).map _).filterMap _ = _
    rw [List.filterMap_map]
    have he : (decodeIndex N I ∘ fun i : Fin N => encoded I K W i.val (events i)) = some := by
      funext i
      exact decode_encoded I K W i (events i) hN
    rw [he, List.filterMap_some]
  rw [hin] at hp
  exact hp

theorem same_cell_order {N : ℕ} (I K W : ℕ) (events : Fin N → Event)
    (hN : N ≤ 2^I) (hcells : ∀ i, cellCode W (events i).cell < 2^K) :
    (sortedIndices I K W events).Pairwise
      (fun i j => (events i).cell = (events j).cell → i ≤ j) := by
  have hs := SortCarrier.sorted_order (request I K W events)
  rw [← sorted_output I K W events hN, List.pairwise_map] at hs
  apply hs.imp
  intro i j hij hcell
  rw [encoded_key, encoded_key] at hij
  have hi : 2*i.val+(events i).after.toNat < 2^(I+1) := by
    have h := i.isLt.trans_le hN
    cases (events i).after <;> simp only [Bool.toNat_false, Bool.toNat_true, pow_succ] <;> omega
  have hj : 2*j.val+(events j).after.toNat < 2^(I+1) := by
    have h := j.isLt.trans_le hN
    cases (events j).after <;> simp only [Bool.toNat_false, Bool.toNat_true, pow_succ] <;> omega
  have ho := (CoordinateKey.key_order (I+1) K _ _ _ _ _ _ hi hj (hcells i) (hcells j)).mp hij
  have he : cellCode W (events i).cell = cellCode W (events j).cell := congrArg (cellCode W) hcell
  change i.val ≤ j.val
  cases hiA : (events i).after <;> cases hjA : (events j).after <;>
    simp only [hiA, hjA, Bool.toNat_false, Bool.toNat_true] at ho <;> omega

theorem sort_run {N : ℕ} (I K W : ℕ) (events : Fin N → Event) (hN : N ≤ 2^I) :
    ∃ r : ExecutionReceipt SortCost.carrier.program.tapeCount SortCost.carrier.program.stateCount,
      LocalBitMultitape.run SortCost.carrier.program.machine
        (128*(N+1)*(I+K+3)^2)
        (SortCost.carrier.program.inputTapes (stream (request I K W events).records)) = some r ∧
      r.final.tapes SortCost.carrier.program.outputTape =
        stream ((sortedIndices I K W events).map (fun i => encoded I K W i.val (events i))) := by
  let req := request I K W events
  obtain ⟨r, hr, hout⟩ := SortCost.carrier.realizes req
  have hn : req.records.length = N := by simp [req, request, DominanceSort.fixedRequest]
  have hw : SortPreparation.width req.records ≤ I+K+2 := by
    have hwords : ∀ r ∈ req.records, (word r).length = I+K+2 := by
      intro r hm
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
      exact encoded_width _ _ _ _ _
    cases he : req.records with
    | nil => simp [SortPreparation.width, SortPreparation.firstWord]
    | cons r rs =>
        have hh := hwords r (by simp [he])
        simp only [SortPreparation.width, SortPreparation.firstWord, hh, Nat.le_refl]
  have hb : 128*(req.records.length+1)*(SortPreparation.width req.records+1)^2 ≤
      128*(N+1)*(I+K+3)^2 := by
    rw [hn]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  refine ⟨r, ?_, ?_⟩
  · have hm := run_moreFuel SortCost.carrier.program.machine
      (128*(req.records.length+1)*(SortPreparation.width req.records+1)^2)
      (128*(N+1)*(I+K+3)^2 - 128*(req.records.length+1)*(SortPreparation.width req.records+1)^2) _ r hr
    rw [Nat.add_sub_of_le hb] at hm
    exact hm
  · rw [sorted_output I K W events hN]
    exact hout

end NearCubicWires.RepairOrdinary.MemorySort
