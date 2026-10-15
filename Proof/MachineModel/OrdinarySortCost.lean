import Proof.MachineModel.OrdinarySortCarrier

/-! Record-count cost at the ordinary sorting consumer. The bound includes
all framing, width production, resets and joins, and is polynomial only in
each record's width, linear in the number of records. -/
namespace NearCubicWires.RepairOrdinary.SortCost
open StablePartition RadixSemantics SortPreparation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem stream_length_of_width (rs : List Record) (bits : ℕ)
    (hw : ∀ r ∈ rs, (word r).length = bits) :
    (stream rs).length = rs.length * (2 * bits + 1) + 1 := by
  have hrecords : (recordsBits rs).length = rs.length * (2 * bits + 1) := by
    induction rs with
    | nil => simp [recordsBits]
    | cons r rs ih =>
      have hr := hw r (by simp)
      have ht := ih (fun a ha => hw a (by simp [ha]))
      have hl : (recordBits r).length = 2 * bits + 1 := by
        change (frame (word r)).length = _
        rw [frame_length, hr]
      simp only [recordsBits, List.flatMap_cons, List.length_append]
      change (recordBits r).length + (recordsBits rs).length = (rs.length + 1) * (2 * bits + 1)
      rw [hl, ht, Nat.add_mul]
      omega
  simp only [stream, List.length_append, hrecords]
  rfl

theorem carrier_budget_le (request : SortCarrier.Request) :
    4 * (stream request.records).length + 3 + SortCarrier.budget request.records ≤
      128 * (request.records.length + 1) * (width request.records + 1) ^ 2 := by
  let count := request.records.length
  let bits := width request.records
  let size := (stream request.records).length
  have hs : size = count * (2 * bits + 1) + 1 :=
    stream_length_of_width request.records bits request.uniform
  have hsize : size + 1 ≤ 2 * (count + 1) * (bits + 1) := by nlinarith
  have hfirst : 4 * size + 3 + SortCarrier.budget request.records ≤
      64 * (size + 1) * (bits + 1) := by
    change 4 * size + 3 + (6 * bits + 6 + 2 * bits * (10 * size + 12)) ≤ _
    nlinarith [Nat.zero_le (bits * size)]
  calc
    _ ≤ 64 * (size + 1) * (bits + 1) := hfirst
    _ ≤ 64 * (2 * (count + 1) * (bits + 1)) * (bits + 1) := by gcongr
    _ = 128 * (request.records.length + 1) * (width request.records + 1) ^ 2 := by
      change 64 * (2 * (count + 1) * (bits + 1)) * (bits + 1) = 128 * (count + 1) * (bits + 1) ^ 2
      ring

noncomputable def carrier : WordFunction SortCarrier.Request (fun request => stream request.records)
    (fun request => stream (SortCarrier.sorted request))
    (fun request => 128 * (request.records.length + 1) * (width request.records + 1) ^ 2) :=
  SortCarrier.carrier.enlargeBudget carrier_budget_le

end NearCubicWires.RepairOrdinary.SortCost
