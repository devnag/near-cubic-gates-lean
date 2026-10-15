import Proof.MachineModel.OrdinaryKeyLabelledScan

/-! Numeric meaning of the exact cell/inner/id keys emitted by KeyLoop.
The id is primary, inner coordinate secondary, and cell payload last. -/
namespace NearCubicWires.RepairOrdinary.CoordinateKey
open SignedSortKey RadixSemantics StablePartition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def key (I K inner id : ℕ) (cell : Bool) : Record := (cell, binary I inner ++ binary K id)
@[simp] theorem key_word (I K inner id : ℕ) (cell : Bool) :
    word (key I K inner id cell) = cell :: (binary I inner ++ binary K id) := rfl
@[simp] theorem key_width (I K inner id : ℕ) (cell : Bool) :
    (word (key I K inner id cell)).length = I + K + 1 := by simp

theorem key_value (I K inner id : ℕ) (cell : Bool) (hi : inner < 2 ^ I) (hd : id < 2 ^ K) :
    value (word (key I K inner id cell)) = cell.toNat + 2 * inner + (2 * 2 ^ I) * id := by
  rw [key_word, value, value_append, binary_value _ _ hi, binary_value _ _ hd, binary_length]
  ring

theorem key_order (I K i j x y : ℕ) (c d : Bool)
    (hi : i < 2 ^ I) (hj : j < 2 ^ I) (hx : x < 2 ^ K) (hy : y < 2 ^ K) :
    value (word (key I K i x c)) ≤ value (word (key I K j y d)) ↔
      x < y ∨ (x = y ∧ (i < j ∨ (i = j ∧ c.toNat ≤ d.toNat))) := by
  have hc : c.toNat < 2 := by cases c <;> decide
  have hd : d.toNat < 2 := by cases d <;> decide
  have hci : c.toNat + 2 * i < 2 * 2 ^ I := by
    have hm := Nat.mul_le_mul_left 2 (show i + 1 ≤ 2 ^ I by omega)
    omega
  have hdj : d.toNat + 2 * j < 2 * 2 ^ I := by
    have hm := Nat.mul_le_mul_left 2 (show j + 1 ≤ 2 ^ I by omega)
    omega
  rw [key_value _ _ _ _ _ hi hx, key_value _ _ _ _ _ hj hy,
    numeric_key_le_iff _ _ _ _ _ hci hdj, numeric_key_le_iff _ _ _ _ _ hc hd]

def generated (K I inner a b : ℕ) (mask : Bool) (records : List KeyLoop.Record) : List Record :=
  records.map (fun r => key I K inner r.2.1 (LeftCell.selected a b r.2.2 mask))

theorem output_records (K I inner a b : ℕ) (mask : Bool) (records : List KeyLoop.Record) :
    KeyLoop.output K I inner a b mask records = recordsBits (generated K I inner a b mask records) := by
  simp [KeyLoop.output, generated, recordsBits, recordBits, key, frame, List.flatMap_map]

theorem output_stream (K I inner a b : ℕ) (mask : Bool) (records : List KeyLoop.Record) :
    KeyLoop.output K I inner a b mask records ++ [false] = stream (generated K I inner a b mask records) := by
  rw [output_records]
  rfl

def request (K I inner a b : ℕ) (mask : Bool) (records : List KeyLoop.Record) : SortCarrier.Request :=
  DominanceSort.fixedRequest (generated K I inner a b mask records) (I + K + 1) (by
    intro r hr
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hr
    exact key_width _ _ _ _ _)

theorem coordinate_index {Gates Buckets : ℕ} (gate : Fin Gates) (bucket : Fin Buckets) :
    (finProdFinEquiv (gate, bucket)).val = gate.val * Buckets + bucket.val := by
  change bucket.val + Buckets * gate.val = _
  ac_rfl

theorem sort_run (K I inner a b : ℕ) (mask : Bool) (records : List KeyLoop.Record) :
    ∃ r : LocalBitMultitape.ExecutionReceipt SortCost.carrier.program.tapeCount SortCost.carrier.program.stateCount,
      LocalBitMultitape.run SortCost.carrier.program.machine
        (128 * (records.length + 1) * (I + K + 2) ^ 2)
        (SortCost.carrier.program.inputTapes (KeyLoop.output K I inner a b mask records ++ [false])) = some r ∧
      r.final.tapes SortCost.carrier.program.outputTape = stream (SortCarrier.sorted (request K I inner a b mask records)) := by
  let req := request K I inner a b mask records
  obtain ⟨r, hr, hout⟩ := SortCost.carrier.realizes req
  have hcount : req.records.length = records.length := by simp [req, request, DominanceSort.fixedRequest, generated]
  have hwidth : SortPreparation.width req.records ≤ I + K + 1 := by
    have hw : ∀ r ∈ req.records, (word r).length = I + K + 1 := by
      intro r hm
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hm
      exact key_width _ _ _ _ _
    cases he : req.records with
    | nil => simp [SortPreparation.width, SortPreparation.firstWord]
    | cons r rs =>
      have hh := hw r (by simp [he])
      simp only [SortPreparation.width, SortPreparation.firstWord, hh, Nat.le_refl]
  have hb : 128 * (req.records.length + 1) * (SortPreparation.width req.records + 1) ^ 2 ≤
      128 * (records.length + 1) * (I + K + 2) ^ 2 := by
    rw [hcount]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  refine ⟨r, ?_, hout⟩
  have he := run_moreFuel SortCost.carrier.program.machine
    (128 * (req.records.length + 1) * (SortPreparation.width req.records + 1) ^ 2)
    (128 * (records.length + 1) * (I + K + 2) ^ 2 -
      128 * (req.records.length + 1) * (SortPreparation.width req.records + 1) ^ 2) _ r hr
  rw [Nat.add_sub_of_le hb] at he
  rw [output_stream]
  exact he

end NearCubicWires.RepairOrdinary.CoordinateKey
